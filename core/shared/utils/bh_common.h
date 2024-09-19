/*
 * Copyright (C) 2019 Intel Corporation.  All rights reserved.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#ifndef _BH_COMMON_H
#define _BH_COMMON_H

#include "bh_platform.h"

#ifdef __cplusplus
extern "C" {
#endif

#define bh_memcpy_s(dest, dlen, src, slen)            \
    do {                                              \
        int _ret = b_memcpy_s(dest, dlen, src, slen); \
        (void)_ret;                                   \
        bh_assert(_ret == 0);                         \
    } while (0)

#define bh_memcpy_wa(dest, dlen, src, slen)            \
    do {                                               \
        int _ret = b_memcpy_wa(dest, dlen, src, slen); \
        (void)_ret;                                    \
        bh_assert(_ret == 0);                          \
    } while (0)

#define bh_memmove_s(dest, dlen, src, slen)            \
    do {                                               \
        int _ret = b_memmove_s(dest, dlen, src, slen); \
        (void)_ret;                                    \
        bh_assert(_ret == 0);                          \
    } while (0)

#define bh_strcat_s(dest, dlen, src)            \
    do {                                        \
        int _ret = b_strcat_s(dest, dlen, src); \
        (void)_ret;                             \
        bh_assert(_ret == 0);                   \
    } while (0)

#define bh_strcpy_s(dest, dlen, src)            \
    do {                                        \
        int _ret = b_strcpy_s(dest, dlen, src); \
        (void)_ret;                             \
        bh_assert(_ret == 0);                   \
    } while (0)

int
b_memcpy_s(void *s1, unsigned int s1max, const void *s2, unsigned int n);
int
b_memcpy_wa(void *s1, unsigned int s1max, const void *s2, unsigned int n);
int
b_memmove_s(void *s1, unsigned int s1max, const void *s2, unsigned int n);
int
b_strcat_s(char *s1, unsigned int s1max, const char *s2);
int
b_strcpy_s(char *s1, unsigned int s1max, const char *s2);

/* strdup with string allocated by BH_MALLOC */
char *
bh_strdup(const char *s);

/* strdup with string allocated by WA_MALLOC */
char *
wa_strdup(const char *s);

static inline uint16
bh_get_uint16(const uint8 *buf)
{
    uint16 ret;
    b_memcpy_s(&ret, sizeof(uint16), buf, sizeof(uint16));
    return ret;
}

static inline uint32
bh_get_uint32(const uint8 *buf)
{
    uint32 ret;
    b_memcpy_s(&ret, sizeof(uint32), buf, sizeof(uint32));
    return ret;
}

static inline uint64
bh_get_uint64(const uint8 *buf)
{
    uint64 ret;
    b_memcpy_s(&ret, sizeof(uint64), buf, sizeof(uint64));
    return ret;
}

static inline uintptr_t
bh_get_uintptr_t(const uint8 *buf)
{
    uintptr_t ret;
    b_memcpy_s(&ret, sizeof(uintptr_t), buf, sizeof(uintptr_t));
    return ret;
}

static inline void
bh_set_uint16(uint8 *buf, uint16 v)
{
    b_memcpy_s(buf, sizeof(uint16), &v, sizeof(uint16));
}

static inline void
bh_set_uint32(uint8 *buf, uint32 v)
{
    b_memcpy_s(buf, sizeof(uint32), &v, sizeof(uint32));
}

static inline void
bh_set_uint64(uint8 *buf, uint64 v)
{
    b_memcpy_s(buf, sizeof(uint64), &v, sizeof(uint64));
}

static inline void
bh_set_uintptr_t(uint8 *buf, uintptr_t v)
{
    b_memcpy_s(buf, sizeof(uintptr_t), &v, sizeof(uintptr_t));
}

#ifdef __cplusplus
}
#endif

#endif
