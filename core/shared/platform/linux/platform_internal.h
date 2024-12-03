/*
 * Copyright (C) 2019 Intel Corporation.  All rights reserved.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#ifndef _PLATFORM_INTERNAL_H
#define _PLATFORM_INTERNAL_H

#include <inttypes.h>
#include <stdbool.h>
#include <assert.h>
#include <time.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdarg.h>
#include <ctype.h>
#include <pthread.h>
#include <signal.h>
#include <semaphore.h>
#include <limits.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <poll.h>
#include <sched.h>
#include <errno.h>
#include <netinet/in.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/timeb.h>
#include <sys/uio.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/resource.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef BH_PLATFORM_LINUX
#define BH_PLATFORM_LINUX
#endif

/* Stack size of applet threads's native part.  */
#define BH_APPLET_PRESERVED_STACK_SIZE (32 * 1024)

/* Default thread priority */
#define BH_THREAD_DEFAULT_PRIORITY 0

typedef pthread_t korp_tid;
typedef pthread_mutex_t korp_mutex;
typedef pthread_cond_t korp_cond;
typedef pthread_t korp_thread;
typedef pthread_rwlock_t korp_rwlock;
typedef sem_t korp_sem;

#define OS_THREAD_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER

#define os_thread_local_attribute __thread

#define bh_socket_t int

#if WASM_DISABLE_WRITE_GS_BASE == 0
#if defined(BUILD_TARGET_X86_64) || defined(BUILD_TARGET_AMD_64)
#define os_writegsbase(base_addr)                                 \
    do {                                                          \
        uint64 __gs_value = (uint64)(uintptr_t)base_addr;         \
        asm volatile("wrgsbase %0" ::"r"(__gs_value) : "memory"); \
    } while (0)
#if 0
/* _writegsbase_u64 also works, but need to add -mfsgsbase flag for gcc */
#include <immintrin.h>
#define os_writegsbase(base_addr) \
    _writegsbase_u64(((uint64)(uintptr_t)base_addr))
#endif
#endif
#endif

#if defined(BUILD_TARGET_X86_64) || defined(BUILD_TARGET_AMD_64)            \
    || defined(BUILD_TARGET_AARCH64) || defined(BUILD_TARGET_RISCV64_LP64D) \
    || defined(BUILD_TARGET_RISCV64_LP64)
/* Enable wasm memory boundary check with hardware trap
   on these 64-bit targets */
#if WASM_DISABLE_MEM_HW_BOUND_CHECK == 0
#define OS_ENABLE_MEM_HW_BOUND_CHECK
#endif
/* Enable native stack boundary check with hardware trap
   on these 64-bit targets */
#if WASM_DISABLE_STACK_HW_BOUND_CHECK == 0
#define OS_ENABLE_STACK_HW_BOUND_CHECK
#endif
#endif

#if defined(BUILD_TARGET_X86_32) || defined(BUILD_TARGET_AMD_32)  \
    || defined(BUILD_TARGET_ARM) || defined(BUILD_TARGET_ARM_VFP) \
    || defined(BUILD_TARGET_RISCV32_ILP32)                        \
    || defined(BUILD_TARGET_RISCV32_ILP32D)                       \
    || defined(BUILD_TARGET_RISCV32_ILP32F) || defined(BUILD_TARGET_XTENSA)
/* Enable native stack boundary check with hardware trap
   on these 32-bit targets */
#if WASM_DISABLE_STACK_HW_BOUND_CHECK == 0
#define OS_ENABLE_STACK_HW_BOUND_CHECK
#endif
#endif

#if defined(OS_ENABLE_MEM_HW_BOUND_CHECK) \
    || defined(OS_ENABLE_STACK_HW_BOUND_CHECK)

#include <setjmp.h>

typedef jmp_buf korp_jmpbuf;

#define os_setjmp setjmp
#define os_longjmp longjmp
#define os_alloca alloca

typedef void (*os_signal_handler)(void *sig_addr);

int
os_thread_signal_init(os_signal_handler handler);

void
os_thread_signal_destroy(void);

bool
os_thread_signal_inited(void);

void
os_signal_unmask(void);

void
os_sigreturn(void);
#endif /* end of defined(OS_ENABLE_MEM_HW_BOUND_CHECK) \
                 || defined(OS_ENABLE_STACK_HW_BOUND_CHECK) */

#define os_getpagesize getpagesize

#if WASM_DISABLE_WAKEUP_BLOCKING_OP == 0
#define OS_ENABLE_WAKEUP_BLOCKING_OP
#endif
void
os_set_signal_number_for_blocking_op(int signo);

typedef int os_file_handle;
typedef DIR *os_dir_stream;
typedef int os_raw_file_handle;

static inline os_file_handle
os_get_invalid_handle(void)
{
    return -1;
}

#ifdef __cplusplus
}
#endif

#endif /* end of _PLATFORM_INTERNAL_H */
