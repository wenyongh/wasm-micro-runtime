/* -*- mode:C; indent-tabs-mode:nil -*- */
/*
 * INTEL CONFIDENTIAL
 *
 * Copyright (C) 2010, 2011 Intel Corporation All Rights Reserved.
 *
 * The source code contained or described herein and all documents
 * related to the source code ("Material") are owned by Intel
 * Corporation or its suppliers or licensors. Title to the Material
 * remains with Intel Corporation or its suppliers and licensors. The
 * Material contains trade secrets and proprietary and confidential
 * information of Intel or its suppliers and licensors. The Material
 * is protected by worldwide copyright and trade secret laws and
 * treaty provisions. No part of the Material may be used, copied,
 * reproduced, modified, published, uploaded, posted, transmitted,
 * distributed, or disclosed in any way without Intel's prior express
 * written permission.
 *
 * No license under any patent, copyright, trade secret or other
 * intellectual property right is granted to or conferred upon you by
 * disclosure or delivery of the Materials, either expressly, by
 * implication, inducement, estoppel or otherwise. Any license under
 * such intellectual property rights must be express and approved by
 * Intel in writing.
 */

/**
 * @file   jit-frontend-jeff.h
 * @author Jiutao <jiu-tao.nie@intel.com>
 * @date   Mon Nov  4 15:26:32 2013
 *
 * @brief  JEFF frontend
 */

#ifndef _INCLUDED_FE_JEFF_JIT_FRONTEND_JEFF_H_
#define _INCLUDED_FE_JEFF_JIT_FRONTEND_JEFF_H_


/**
 * Relocation types and modifiers for JEFF frontend.
 */
enum
  {
    /* Relocation types.  */
    JEFF_REL_NONE       = 0x00, /* no relocation info */
    JEFF_REL_BCIP       = 0x01, /* bytecode instruction pointer */
    JEFF_REL_CLASS      = 0x02, /* class from offset (0 for current class) */
    JEFF_REL_METHOD     = 0x03, /* method from offset (0 for current method) */
    JEFF_REL_FIELD      = 0x04, /* field from offset */
    JEFF_REL_CLASSIDX   = 0x05, /* class from class index in the package */
    JEFF_REL_INTRINSIC  = 0x06, /* intrinsic function */

    /* Relocation types defined in codegen, not from FE.
     * This is required when calcuating relocation info
     * in jit-frondend-jeff-lower.c
     * and the value must equal to same definition in cg-intrinisic.h
     */
    JIT_REL_CG_INTRINSIC = 0x0a, /* intrinsic from codegen */

    /* Below values are modifiers to above ones.  */
    JEFF_REL_MOD_NONE   = 0x00, /* get original entity */
    JEFF_REL_MOD_CLASS  = 0x10, /* get class of original entity */
    JEFF_REL_MOD_FLDOFF = 0x20, /* get offset of field */
    JEFF_REL_MOD_MTDIDX = 0x30, /* get vtable index of method */
    JEFF_REL_MOD_MTDOFF = 0x40, /* get vtable offset of method */
    JEFF_REL_MOD_SPEMTD = 0x50, /* get method for INVOKESPECIAL */
    JEFF_REL_MOD_FIL    = 0x60, /* get FIL offset of original entity */
    JEFF_REL_MOD_CIL    = 0x70  /* get CIL offset of original entity */
  };

/**
 * Create a constant register without relocation info.
 *
 * @param Type type of the register
 * @param val the constant value
 *
 * @return the constant register if succeeds, 0 otherwise
 */
#define NEW_CONST(Type, val)                    \
  jit_cc_new_const_##Type (cc, val)

#define NEW_REL_INFO(T, M, r)                                   \
  (((JEFF_REL_##T | JEFF_REL_MOD_##M) << 16) | ((r) & 0xffff))
#define GET_REL_TYPE(reloc_info)    (((reloc_info) >> 16) & 0x0f)
#define GET_REL_MOD(reloc_info)     (((reloc_info) >> 16) & 0xf0)
#define GET_REL_DATA(reloc_info)    ((reloc_info) & 0xffff)

/**
 * Create a constant register with relocation info.  It can also be
 * used for changing relocation modifier to an existing relocation
 * info by passing NONE as relocation type.
 *
 * @param T relocation type
 * @param M relocation modifier
 * @param r relocation data for reconstructing the value
 * @param v the constant value
 *
 * @return the constant register if succeeds, 0 otherwise
 */
#define NEW_REL(T, M, r, v)                                     \
  jit_cc_new_const_I4_rel (cc, (int32)(v),                      \
                           (jit_globals.options.aot_gen_mode    \
                            ? NEW_REL_INFO (T, M, r) : 0))

#define NEW_INTRINSIC(Name)                                             \
  NEW_REL (INTRINSIC, NONE, JIT_FRONTEND_JEFF_INTRINSIC_##Name, Name)

/**
 * Intrinsic function indexes.
 */
enum
  {
#define INTRINSIC(NAME) JIT_FRONTEND_JEFF_INTRINSIC_##NAME,
#include "jit-frontend-jeff-intrinsic.def"
#undef INTRINSIC
    JIT_FRONTEND_JEFF_INTRINSIC_NUM
  };

/**
 * Calculate the offsets of file instance local and class instance
 * local data to the base address.
 */
#define GET_FIL_OFFSET(uid) (sizeof (JeffFileInstanceLocal *) * (uid))
#define GET_CIL_OFFSET(idx) (offsetof (JeffFileInstanceLocal, class_ils) \
                             + sizeof (JeffClassInstanceLocal *) * (idx))


#endif
