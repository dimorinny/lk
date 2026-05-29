/*
 * Copyright (C) 2024 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
#include "boot_service_provider.h"

#include <kernel/mutex.h>
#include <lk/compiler.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <platform.h>
#include <sys/types.h>
#include <uefi/boot_service.h>
#include <uefi/protocols/block_io_protocol.h>
#include <uefi/protocols/dt_fixup_protocol.h>
#include <uefi/protocols/gbl_efi_image_loading_protocol.h>
#include <uefi/protocols/gbl_efi_os_configuration_protocol.h>
#include <uefi/protocols/loaded_image_protocol.h>
#include <uefi/types.h>

#include "blockio2_protocols.h"
#include "blockio_protocols.h"
#include "events.h"
#include "io_stack.h"
#include "memory_protocols.h"
#include "uefi_platform.h"

namespace {

EfiStatus unload(EfiHandle handle) { return EFI_STATUS_SUCCESS; }

bool guid_eq(const EfiGuid *a, const EfiGuid *b) {
  return memcmp(a, b, sizeof(*a)) == 0;
}

bool guid_eq(const EfiGuid *a, const EfiGuid &b) {
  return memcmp(a, &b, sizeof(*a)) == 0;
}

// ---------------------------------------------------------------------------
// Protocol interface cache (install-once semantics).
//
// Background: open_protocol previously synthesized (malloc'd) a fresh interface
// struct on every call, and close_protocol is a no-op, so repeated opens of the
// same protocol leaked one struct each. UEFI guarantees a single interface per
// (handle, GUID); the open attributes / agent / controller do NOT change the
// returned interface, so they are intentionally excluded from the cache key.
// This mirrors EDK2/U-Boot, which return the one shared interface regardless of
// attribute. The cache bounds memory to one interface per (handle, GUID) for
// the lifetime of boot services; like EDK2/U-Boot (which free at
// UninstallProtocolInterface, never called here) the interfaces persist until
// the whole UEFI environment is torn down at OS handoff, when the bootloader
// heap / BOOT_SERVICES_DATA is reclaimed. That is why close_protocol can remain
// a no-op.
//
// Scope: only protocols whose interface open_protocol builds in-line and which
// carry no per-open mutable state are cached (see is_cacheable_protocol). The
// delegated, stateful protocols (block-io, async block-io, erase-block,
// boot-memory) are deliberately NOT cached: they perform real per-open work
// (bio_open, worker threads, io-stack setup) and must keep their original
// per-open semantics. Caching only the safe, stateless descriptors means the
// fix can never change the behavior of the I/O paths.
//
// Attributes (EXCLUSIVE / BY_DRIVER) are not interpreted: LK has no UEFI driver
// model, so the access-control and DisconnectController side effects those
// attributes trigger in EDK2/U-Boot are no-ops here -- exactly as in the
// original implementation. This cache changes only allocation behavior, never
// attribute behavior.
// ---------------------------------------------------------------------------
struct CachedProtocol {
  EfiHandle handle;
  EfiGuid guid;
  const void *interface;
};

constexpr size_t kProtocolCacheCap = 64;
CachedProtocol g_protocol_cache[kProtocolCacheCap];
size_t g_protocol_cache_count = 0;
size_t g_protocol_alloc_count = 0;  // diagnostics: real allocations performed
size_t g_protocol_hit_count = 0;    // diagnostics: cache hits served
// Serializes check-then-insert against the (handle,GUID) cache. Today boot
// services are only invoked from the single UEFI application thread (the async
// block-io worker threads never call open_protocol), so this lock is defensive
// rather than load-bearing -- but it is cheap and future-proofs the global
// table against any later caller. Must only be taken from thread context;
// open_protocol is never reached from interrupt/notify context.
Mutex g_protocol_cache_lock;

// Stateless descriptor protocols that are safe to cache and share. Anything not
// listed falls through to per-open allocation (the original behavior), so the
// safe default for a newly added protocol is "not cached".
bool is_cacheable_protocol(const EfiGuid *protocol) {
  return guid_eq(protocol, LOADED_IMAGE_PROTOCOL_GUID) ||
         guid_eq(protocol, EFI_DT_FIXUP_PROTOCOL_GUID) ||
         guid_eq(protocol, EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID) ||
         guid_eq(protocol, EFI_TIMESTAMP_PROTOCOL_GUID);
}

// Caller must hold g_protocol_cache_lock.
const void *protocol_cache_lookup(EfiHandle handle, const EfiGuid *protocol) {
  for (size_t i = 0; i < g_protocol_cache_count; ++i) {
    if (g_protocol_cache[i].handle == handle &&
        guid_eq(protocol, &g_protocol_cache[i].guid)) {
      return g_protocol_cache[i].interface;
    }
  }
  return nullptr;
}

// Caller must hold g_protocol_cache_lock.
void protocol_cache_store(EfiHandle handle, const EfiGuid *protocol,
                          const void *interface) {
  if (g_protocol_cache_count >= kProtocolCacheCap) {
    // Cache full: fall back to per-open allocation. Still correct, just not
    // deduplicated (the original leak reappears for further unique keys). 64
    // (handle,GUID) pairs is far more than a boot ever needs, so warn once if
    // we ever hit it -- it signals an unexpected usage pattern, not a normal
    // condition.
    static bool warned = false;
    if (!warned) {
      warned = true;
      printf("[proto-cache] WARNING: cache full at %zu entries; further unique "
             "(handle,GUID) opens fall back to per-open allocation\n",
             kProtocolCacheCap);
    }
    return;
  }
  CachedProtocol &slot = g_protocol_cache[g_protocol_cache_count++];
  slot.handle = handle;
  slot.guid = *protocol;
  slot.interface = interface;
}

EfiStatus handle_protocol(EfiHandle handle, const EfiGuid *protocol,
                          void **intf) {
  if (guid_eq(protocol, LOADED_IMAGE_PROTOCOL_GUID)) {
    printf("handle_protocol(%p, LOADED_IMAGE_PROTOCOL_GUID, %p);\n", handle,
           intf);
    const auto loaded_image = static_cast<EfiLoadedImageProtocol *>(uefi_malloc(sizeof(EfiLoadedImageProtocol)));
    if (!loaded_image) {
      return EFI_STATUS_OUT_OF_RESOURCES;
    }
    *loaded_image = {};
    loaded_image->revision = EFI_LOADED_IMAGE_PROTOCOL_REVISION;
    loaded_image->parent_handle = nullptr;
    loaded_image->system_table = nullptr;
    loaded_image->load_options_size = 0;
    loaded_image->load_options = nullptr;
    loaded_image->unload = unload;
    loaded_image->image_base = handle;

    *intf = loaded_image;
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, LINUX_EFI_LOADED_IMAGE_FIXED_GUID)) {
    printf("handle_protocol(%p, LINUX_EFI_LOADED_IMAGE_FIXED_GUID, %p);\n",
           handle, intf);
    return EFI_STATUS_UNSUPPORTED;
  } else {
    printf("handle_protocol(%p, %p, %p);\n", handle, protocol, intf);
  }
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus register_protocol_notify(const EfiGuid *protocol, EfiEvent event,
                                   void **registration) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus locate_handle(EfiLocateHandleSearchType search_type,
                        const EfiGuid *protocol, const void *search_key,
                        size_t *buf_size, EfiHandle *buf) {

  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus locate_protocol(const EfiGuid *protocol, void *registration,
                          void **intf) {
  if (protocol == nullptr) {
    return EFI_STATUS_INVALID_PARAMETER;
  }
  if (memcmp(protocol, &EFI_RNG_PROTOCOL_GUID, sizeof(*protocol)) == 0) {
    printf("%s(EFI_RNG_PROTOCOL_GUID) is unsupported.\n", __FUNCTION__);
    return EFI_STATUS_UNSUPPORTED;
  }
  if (memcmp(protocol, &EFI_TCG2_PROTOCOL_GUID, sizeof(*protocol)) == 0) {
    printf("%s(EFI_TCG2_PROTOCOL_GUID) is unsupported.\n", __FUNCTION__);
    return EFI_STATUS_NOT_FOUND;
  }

  printf("%s(%x %x %x %llx) is unsupported\n", __FUNCTION__, protocol->data1,
         protocol->data2, protocol->data3,
         *reinterpret_cast<const uint64_t *>(&protocol->data4));
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus uninstall_multiple_protocol_interfaces(EfiHandle handle, ...) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}
EfiStatus calculate_crc32(void *data, size_t len, uint32_t *crc32) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus uninstall_protocol_interface(EfiHandle handle,
                                       const EfiGuid *protocol, void *intf) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus load_image(bool boot_policy, EfiHandle parent_image_handle,
                     EfiDevicePathProtocol *path, void *src, size_t src_size,
                     EfiHandle *image_handle) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus locate_device_path(const EfiGuid *protocol,
                             EfiDevicePathProtocol **path, EfiHandle *device) {
  if (memcmp(protocol, &EFI_LOAD_FILE2_PROTOCOL_GUID,
             sizeof(EFI_LOAD_FILE2_PROTOCOL_GUID)) == 0) {
    return EFI_STATUS_NOT_FOUND;
  }
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus install_configuration_table(const EfiGuid *guid, void *table) {
  printf("%s is unsupported\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

void copy_mem(void *dest, const void *src, size_t len) {
  memcpy(dest, src, len);
}
void set_mem(void *buf, size_t len, uint8_t val) { memset(buf, val, len); }

EfiTpl raise_tpl(EfiTpl new_tpl) {
  printf("%s is called %zu\n", __FUNCTION__, new_tpl);
  return EFI_TPL_APPLICATION;
}

void restore_tpl(EfiTpl old_tpl) {
  printf("%s is called %zu\n", __FUNCTION__, old_tpl);
}

EfiStatus open_protocol_uncached(EfiHandle handle, const EfiGuid *protocol,
                                 const void **intf, EfiHandle agent_handle,
                                 EfiHandle controller_handle,
                                 EfiOpenProtocolAttributes attr) {
  if (guid_eq(protocol, LOADED_IMAGE_PROTOCOL_GUID)) {
    auto interface = reinterpret_cast<EfiLoadedImageProtocol *>(
        uefi_malloc(sizeof(EfiLoadedImageProtocol)));
    if (interface == nullptr) {
      return EFI_STATUS_OUT_OF_RESOURCES;
    }
    memset(interface, 0, sizeof(*interface));
    // Keep this identical to handle_protocol()'s LOADED_IMAGE construction:
    // both APIs must hand back an equivalent, spec-valid interface (matching
    // EDK2/U-Boot, where HandleProtocol == OpenProtocol(BY_HANDLE_PROTOCOL)).
    // Notably set `revision` and `unload`, which the cache would otherwise
    // freeze at 0/NULL and break a consumer that checks revision or unloads.
    interface->revision = EFI_LOADED_IMAGE_PROTOCOL_REVISION;
    interface->image_base = handle;
    interface->unload = unload;
    *intf = interface;
    printf("%s(LOADED_IMAGE_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_DEVICE_PATH_PROTOCOL_GUID)) {
    printf("%s(EFI_DEVICE_PATH_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return EFI_STATUS_UNSUPPORTED;
  } else if (guid_eq(protocol, EFI_BLOCK_IO_PROTOCOL_GUID)) {
    printf("%s(EFI_BLOCK_IO_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return open_block_device(handle, intf);
  } else if (guid_eq(protocol, EFI_BLOCK_IO2_PROTOCOL_GUID)) {
    printf("%s(EFI_BLOCK_IO2_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return open_async_block_device(handle, intf);
  } else if (guid_eq(protocol, EFI_DT_FIXUP_PROTOCOL_GUID)) {
    printf("%s(EFI_DT_FIXUP_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    if (intf != nullptr) {
      EfiDtFixupProtocol *fixup = nullptr;
      allocate_pool(EFI_MEMORY_TYPE_BOOT_SERVICES_DATA, sizeof(EfiDtFixupProtocol),
                    reinterpret_cast<void **>(&fixup));
      if (fixup == nullptr) {
        return EFI_STATUS_OUT_OF_RESOURCES;
      }
      fixup->revision = EFI_DT_FIXUP_PROTOCOL_REVISION;
      fixup->fixup = efi_dt_fixup;
      *intf = reinterpret_cast<void *>(fixup);
    }
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID)) {
    printf("%s(EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID, handle=%p, "
           "agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    GblEfiOsConfigurationProtocol *config = nullptr;
    allocate_pool(EFI_MEMORY_TYPE_BOOT_SERVICES_DATA, sizeof(*config),
                  reinterpret_cast<void **>(&config));
    if (config == nullptr) {
      return EFI_STATUS_OUT_OF_RESOURCES;
    }
    config->revision = GBL_EFI_OS_CONFIGURATION_PROTOCOL_REVISION;
    config->fixup_bootconfig = fixup_bootconfig;
    config->select_device_trees = select_device_trees;
    config->select_fit_configuration = select_fit_configuration;
    *intf = reinterpret_cast<void *>(config);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_GBL_EFI_IMAGE_LOADING_PROTOCOL_GUID)) {
    printf(
        "%s(EFI_GBL_EFI_IMAGE_LOADING_PROTOCOL_GUID, handle=%p, "
        "agent_handle%p, controller_handle=%p, attr=0x%x)\n",
        __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return EFI_STATUS_UNSUPPORTED;
  } else if (guid_eq(protocol, EFI_TIMESTAMP_PROTOCOL_GUID)) {
    printf("%s(EFI_TIMESTAMP_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    EfiTimestampProtocol *ts = reinterpret_cast<EfiTimestampProtocol *>(
        uefi_malloc(sizeof(EfiTimestampProtocol)));
    if (ts == nullptr) {
      return EFI_STATUS_OUT_OF_RESOURCES;
    }
    ts->get_timestamp = get_timestamp;
    ts->get_properties = get_timestamp_properties;
    *intf = reinterpret_cast<void *>(ts);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_ERASE_BLOCK_PROTOCOL_GUID)) {
    printf("%s(EFI_ERASE_BLOCK_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p, attr=0x%x)\n",
           __FUNCTION__, handle, agent_handle, controller_handle, attr);
    return open_efi_erase_block_protocol(handle, intf);
  } else if (guid_eq(protocol, EFI_BOOT_MEMORY_PROTOCOL_GUID)) {
    printf(
        "%s(EFI_BOOT_MEMORY_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
        "controller_handle=%p, attr=0x%x)\n",
        __FUNCTION__, handle, agent_handle, controller_handle, attr);
    *intf = open_boot_memory_protocol();
    if (*intf == nullptr) {
      return EFI_STATUS_OUT_OF_RESOURCES;
    }
    return EFI_STATUS_SUCCESS;
  }
  printf("%s is unsupported 0x%x 0x%x 0x%x 0x%llx\n", __FUNCTION__,
         protocol->data1, protocol->data2, protocol->data3,
         *(uint64_t *)&protocol->data4);
  return EFI_STATUS_UNSUPPORTED;
}

// Caching front-end for open_protocol: for the stateless descriptor protocols
// (is_cacheable_protocol) it returns the interface created on the first open of
// a given (handle, GUID) instead of allocating a new one every time. All other
// protocols, and calls that don't take an output pointer, go straight to the
// original per-open path unchanged.
EfiStatus open_protocol(EfiHandle handle, const EfiGuid *protocol,
                        const void **intf, EfiHandle agent_handle,
                        EfiHandle controller_handle,
                        EfiOpenProtocolAttributes attr) {
  if (intf == nullptr || !is_cacheable_protocol(protocol)) {
    return open_protocol_uncached(handle, protocol, intf, agent_handle,
                                  controller_handle, attr);
  }

  // Hold the lock across lookup + allocate + store so two threads can't both
  // miss and insert duplicate entries for the same (handle, GUID).
  AutoLock guard{&g_protocol_cache_lock};

  const void *cached = protocol_cache_lookup(handle, protocol);
  if (cached != nullptr) {
    *intf = cached;
    ++g_protocol_hit_count;
    return EFI_STATUS_SUCCESS;
  }

  EfiStatus status = open_protocol_uncached(handle, protocol, intf, agent_handle,
                                            controller_handle, attr);
  if (status == EFI_STATUS_SUCCESS && *intf != nullptr) {
    ++g_protocol_alloc_count;
    protocol_cache_store(handle, protocol, *intf);
  }
  return status;
}

EfiStatus close_protocol(EfiHandle handle, const EfiGuid *protocol,
                         EfiHandle agent_handle, EfiHandle controller_handle) {
  if (guid_eq(protocol, LOADED_IMAGE_PROTOCOL_GUID)) {
    printf("%s(LOADED_IMAGE_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p)\n",
           __FUNCTION__, handle, agent_handle, controller_handle);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_DEVICE_PATH_PROTOCOL_GUID)) {
    printf("%s(EFI_DEVICE_PATH_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p)\n",
           __FUNCTION__, handle, agent_handle, controller_handle);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_BLOCK_IO_PROTOCOL_GUID)) {
    printf("%s(EFI_BLOCK_IO_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p)\n",
           __FUNCTION__, handle, agent_handle, controller_handle);
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_DT_FIXUP_PROTOCOL_GUID)) {
    printf("%s(EFI_DT_FIXUP_PROTOCOL_GUID, handle=%p, agent_handle=%p, "
           "controller_handle=%p)\n",
           __FUNCTION__, handle, agent_handle, controller_handle);
    return EFI_STATUS_SUCCESS;
  }
  printf("%s is called\n", __FUNCTION__);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus locate_handle_buffer(EfiLocateHandleSearchType search_type,
                               const EfiGuid *protocol, const void *search_key,
                               size_t *num_handles, EfiHandle **buf) {
  if (guid_eq(protocol, EFI_BLOCK_IO_PROTOCOL_GUID)) {
    if (search_type == EFI_LOCATE_HANDLE_SEARCH_TYPE_BY_PROTOCOL) {
      return list_block_devices(num_handles, buf);
    }
    printf("%s(0x%x, EFI_BLOCK_IO_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    return EFI_STATUS_UNSUPPORTED;
  } else if (guid_eq(protocol, EFI_TEXT_INPUT_PROTOCOL_GUID)) {
    printf("%s(0x%x, EFI_TEXT_INPUT_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    return EFI_STATUS_NOT_FOUND;
  } else if (guid_eq(protocol, EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID)) {
    printf("%s(0x%x, EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    if (num_handles != nullptr) {
      *num_handles = 1;
    }
    if (buf != nullptr) {
      *buf = reinterpret_cast<EfiHandle *>(uefi_malloc(sizeof(buf)));
    }
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_DT_FIXUP_PROTOCOL_GUID)) {
    printf("%s(0x%x, EFI_DT_FIXUP_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    if (num_handles != nullptr) {
      *num_handles = 1;
    }
    if (buf != nullptr) {
      *buf = reinterpret_cast<EfiHandle *>(uefi_malloc(sizeof(buf)));
    }
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_TIMESTAMP_PROTOCOL_GUID)) {
    printf("%s(0x%x, EFI_TIMESTAMP_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    if (num_handles != nullptr) {
      *num_handles = 1;
    }
    if (buf != nullptr) {
      *buf = reinterpret_cast<EfiHandle *>(uefi_malloc(sizeof(buf)));
    }
    return EFI_STATUS_SUCCESS;
  } else if (guid_eq(protocol, EFI_BOOT_MEMORY_PROTOCOL_GUID)) {
    printf("%s(0x%x, EFI_BOOT_MEMORY_PROTOCOL_GUID, search_key=%p)\n",
           __FUNCTION__, search_type, search_key);
    if (num_handles != nullptr) {
      *num_handles = 1;
    }
    if (buf != nullptr) {
      *buf = reinterpret_cast<EfiHandle*>(uefi_malloc(sizeof(buf)));
    }
    return EFI_STATUS_SUCCESS;
  }
  printf("%s(0x%x, (0x%x 0x%x 0x%x 0x%llx), search_key=%p)\n", __FUNCTION__,
         search_type, protocol->data1, protocol->data2, protocol->data3,
         *(uint64_t *)&protocol->data4, search_key);
  return EFI_STATUS_UNSUPPORTED;
}

EfiStatus stall(size_t microseconds) {
  uint64_t end_microseconds;

  end_microseconds = current_time_hires() + microseconds;
  while (current_time_hires() < end_microseconds) {
    thread_yield();
  }

  return EFI_STATUS_SUCCESS;
}

EfiStatus free_pages(EfiPhysicalAddr memory, size_t pages) {
  // NOLINTNEXTLINE(performance-no-int-to-ptr)
  return ::free_pages(reinterpret_cast<void *>(memory), pages);
}

} // namespace

#if WITH_TESTS
// Console self-test for the protocol cache (`uefi_proto_test`). Demonstrates
// that repeated opens of the same (handle, GUID) allocate exactly once, while
// a different handle or a different GUID allocate separately. Test/debug builds
// only -- it drives the real open_protocol with synthetic handles, so it must
// never be compiled into a production image.
void uefi_protocol_cache_selftest() {
  // Use fresh synthetic handles on every invocation so the test is idempotent:
  // re-running it must not be skewed by entries cached by a previous run.
  // Disjoint A/B ranges: the base gap (0x10000000) vastly exceeds the per-run
  // stride (0x10000), so handle_a(N) never aliases handle_b(M) within any
  // realistic number of runs.
  static uintptr_t run = 0;
  ++run;
  const EfiHandle handle_a =
      reinterpret_cast<EfiHandle>(0x10000000 + run * 0x10000);
  const EfiHandle handle_b =
      reinterpret_cast<EfiHandle>(0x20000000 + run * 0x10000);
  const auto attr = static_cast<EfiOpenProtocolAttributes>(0);
  const size_t alloc_base = g_protocol_alloc_count;
  const size_t hit_base = g_protocol_hit_count;

  printf("\n[proto-cache] ==== self-test start (allocs so far=%zu) ====\n",
         alloc_base);

  // Open OS_CONFIGURATION on the same handle 4 times.
  const void *first = nullptr;
  bool ptr_stable = true;
  for (int i = 0; i < 4; ++i) {
    const void *p = nullptr;
    open_protocol(handle_a, &EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID, &p, nullptr,
                  nullptr, attr);
    if (i == 0) {
      first = p;
    } else if (p != first) {
      ptr_stable = false;
    }
  }
  const size_t allocs_same = g_protocol_alloc_count - alloc_base;
  const size_t hits_same = g_protocol_hit_count - hit_base;

  // Different handle -> must allocate again (handle is part of the key).
  const void *pb = nullptr;
  open_protocol(handle_b, &EFI_GBL_OS_CONFIGURATION_PROTOCOL_GUID, &pb, nullptr,
                nullptr, attr);
  // Different GUID on the original handle -> must allocate again.
  const void *pd = nullptr;
  open_protocol(handle_a, &EFI_DT_FIXUP_PROTOCOL_GUID, &pd, nullptr, nullptr,
                attr);

  const size_t allocs_total = g_protocol_alloc_count - alloc_base;
  const bool pass = ptr_stable && allocs_same == 1 && hits_same == 3 &&
                    allocs_total == 3 && pb != first && pd != first;

  printf("[proto-cache] 4x same (handle,GUID): pointer_stable=%s allocations=%zu "
         "(expect 1) hits=%zu (expect 3)\n",
         ptr_stable ? "yes" : "NO", allocs_same, hits_same);
  printf("[proto-cache] + new handle + new GUID: total allocations=%zu "
         "(expect 3)\n",
         allocs_total);
  printf("[proto-cache] RESULT: %s  (4 opens of one protocol => 1 alloc; "
         "without the cache this would be 6 allocs / 6 leaks)\n",
         pass ? "PASS" : "FAIL");
  printf("[proto-cache] ==== self-test end ====\n\n");
}
#endif  // WITH_TESTS

void setup_boot_service_table(EfiBootService *service) {
  service->handle_protocol = handle_protocol;
  service->allocate_pool = allocate_pool;
  service->free_pool = free_pool;
  service->get_memory_map = get_physical_memory_map;
  service->register_protocol_notify = register_protocol_notify;
  service->locate_handle = locate_handle;
  service->locate_protocol = locate_protocol;
  service->allocate_pages = allocate_pages;
  service->free_pages = free_pages;
  service->uninstall_multiple_protocol_interfaces =
      uninstall_multiple_protocol_interfaces;
  service->calculate_crc32 = calculate_crc32;
  service->uninstall_protocol_interface = uninstall_protocol_interface;
  service->load_image = load_image;
  service->locate_device_path = locate_device_path;
  service->install_configuration_table = install_configuration_table;
  service->exit_boot_services = exit_boot_services;
  service->copy_mem = copy_mem;
  service->set_mem = set_mem;
  service->open_protocol = open_protocol;
  service->locate_handle_buffer = locate_handle_buffer;
  service->close_protocol = close_protocol;
  service->wait_for_event =
      switch_stack_wrapper<size_t, EfiEvent *, size_t *, wait_for_event>();
  service->signal_event = switch_stack_wrapper<EfiEvent, signal_event>();
  service->check_event = switch_stack_wrapper<EfiEvent, check_event>();
  service->create_event = create_event;
  service->close_event = close_event;
  service->stall = stall;
  service->raise_tpl = raise_tpl;
  service->restore_tpl = restore_tpl;
  service->set_watchdog_timer = set_watchdog_timer;
}
