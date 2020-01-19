LOCAL_DIR := $(GET_LOCAL_DIR)

MODULE := $(LOCAL_DIR)

PLATFORM := sifive
VARIANT := sifive_e
WITH_LINKER_GC ?= 1

MEMSIZE ?= 0x4000     # 16KB
GLOBAL_DEFINES += TARGET_HAS_DEBUG_LED=1

# target code will set the master frequency to 16Mhz
GLOBAL_DEFINES += SIFIVE_FREQ=16000000

MODULE_SRCS := $(LOCAL_DIR)/target.c

# set some global defines based on capability
GLOBAL_DEFINES += PLATFORM_HAS_DYNAMIC_TIMER=1
GLOBAL_DEFINES += ARCH_RISCV_CLINT_BASE=0x02000000
GLOBAL_DEFINES += ARCH_RISCV_MTIME_RATE=32768

include make/module.mk

