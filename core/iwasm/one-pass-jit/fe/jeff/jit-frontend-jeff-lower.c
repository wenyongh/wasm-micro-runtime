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
 * @file   jit-frontend-jeff-lower.c
 * @author Jiutao <jiu-tao.nie@intel.com>
 * @date   Mon May  6 12:42:58 2013
 *
 * @brief  Lower pass of JEFF front end
 */

#include "../../vmcore_jeff/jeff-runtime.h"
#include "../../vmcore_jeff/jeff-thread.h"
#include "../../vmcore_jeff/jeff-opcode.h"
#include "../../vmcore_jeff/jeff-interp.h"
#include "../../vmcore_jeff/jeff-sync.h"
#include "../jit/cg/cg-intrinsic.h"

#include "jit-export.h"
#include "jit-ir.h"
#include "jit-frontend.h"
#include "jit-frontend-jeff.h"

#ifdef BH_VXWORKS
#undef NONE
#endif

/**
 * Helper function for GEN_INSN
 *
 * @param cc compilation context
 * @param insn the instruction to insert before
 * @param new_insn the new instruction
 *
 * @return the new instruction if inserted, NULL otherwise
 */
static inline JitInsn*
_gen_insn (JitCompContext *cc, JitInsn *insn, JitInsn *new_insn)
{
  if (new_insn)
    jit_insn_insert_before (insn, new_insn);

  return new_insn;
}

/**
 * Generate an instruction insert before insn.
 */
#define GEN_INSN(...)                                       \
  _gen_insn (cc, insn, jit_cc_new_insn (cc, __VA_ARGS__))


/**
 * Insert a block for exception handling.
 *
 * @param cc the compilation context
 * @param chk_insn the CHK instruction.  If it's NULL, then no need to
 * save the BCIP address.
 * @param action interpreter action
 * @param index array index for AIOOBE
 *
 * @return label of the new block if succeeds, 0 otherwise
 */
static JitReg
insert_exception_block (JitCompContext *cc, JitInsn *chk_insn,
                        unsigned action, JitReg index)
{
  JitBlock *block;
  JitInsn *insn;
  JitReg bcip = chk_insn ? *(jit_insn_opnd (chk_insn, 0)) : 0;

  if (!(block = jit_cc_new_block (cc, 0)))
    return 0;

  insn = jit_block_last_insn (block);

  if (chk_insn)
    {
      JitReg ip = 0;
      JitReg ip_offset = NEW_CONST (I4, offsetof (JeffInterpFrame, ip));

      /* Commit frame ip before return to interpreter */
      switch (chk_insn->opcode)
        {
          case JIT_OP_CHKZERO:
          case JIT_OP_CHKNULL:
            ip = *jit_insn_opnd (chk_insn, 2);
            GEN_INSN (STI4, ip, cc->fp_reg, ip_offset);
            break;
          case JIT_OP_CHKARRIDX:
          case JIT_OP_CHKARRVAL:
            ip = *jit_insn_opnd (chk_insn, 3);
            GEN_INSN (STI4, ip, cc->fp_reg, ip_offset);
            break;
          case JIT_OP_CHKCAST:
            ip = *jit_insn_opnd (chk_insn, 4);
            GEN_INSN (STI4, ip, cc->fp_reg, ip_offset);
            break;
        }
    }

  GEN_INSN (LEAVE, NEW_CONST (I4, action), bcip, index);

  return jit_block_label (block);
}

/**
 * Get the common THROWN leaving block that doesn't need bcip.
 *
 * @param cc the compilation context
 *
 * @return the common THROWN leaving block that doesn't need bcip
 */
static JitReg
get_common_thrown_block (JitCompContext *cc)
{
  JitBlock *block = (JitBlock *)cc->pass_local_data;
  JitInsn *insn;

  if (!block)
    {
      if (!(block = jit_cc_new_block (cc, 0)))
        return 0;

      insn = jit_block_last_insn (block);
      GEN_INSN (LEAVE,
                NEW_CONST (I4, JIT_INTERP_ACTION_THROWN),
                NEW_CONST (I4, -1), 0);
    }

  return jit_block_label (block);
}

#if BEIHAI_ENABLE_JIT_LLVM != 0
static JitReg
get_leave_from_callbc_block (JitCompContext *cc, JitReg action)
{
  JitBlock *block = jit_cc_new_block (cc, 0);
  JitInsn *insn;

  if (!block)
    return 0;

  insn = jit_block_last_insn (block);
#if BEIHAI_ENABLE_JIT_BH_CODEGEN != 0
  GEN_INSN (LEAVEFROMCALLBC, 0);
#else
  GEN_INSN (LEAVEFROMCALLBC, action);
#endif
  return jit_block_label (block);
}
#endif

static JitInsn*
lower_one_insn (JitCompContext *cc, JitBlock *block, JitInsn *insn)
{
  JitInsn *insn1 = NULL;

  switch (insn->opcode)
    {
    case JIT_OP_CLASSBASE:
      {
        JitReg lhs = *(jit_insn_opnd (insn, 0));
        JitReg rhs = *(jit_insn_opnd (insn, 1));
        JeffClassHeaderLinked *clz =
          (JeffClassHeaderLinked *)jit_cc_get_const_I4 (cc, rhs);
        unsigned clz_rel = jit_cc_get_const_I4_rel (cc, rhs);

#ifndef BH_OPENJDK /* The thread list need to be locked when accessing file_il_vector,
                     it is a bug when there are many jeff files to load */
        if (clz == jeff_get_method_class ((JeffMethodLinked *)cc->method))
          /* The target class is same as the current method's class,
             the class's instance local area must have existed.  */
          {
            JitReg ilr = jit_cc_new_reg_I4 (cc);
            JitReg elm = jit_cc_new_reg_I4 (cc);
            JitReg fil = jit_cc_new_reg_I4 (cc);
            unsigned uid = jeff_runtime_file_to_fuid (jeff_get_file_header (clz));
            unsigned idx = jeff_get_class_index (clz, clz->this_class_index);

            GEN_INSN (LDI4, ilr, cc->self_reg,
                      NEW_CONST (I4, offsetof (JeffThread, vm_instance)));
            GEN_INSN (LDI4, elm, ilr,
                      NEW_CONST (I4, offsetof (JeffVmInstance,
                                               file_il_vector.elements)));

            if (GET_REL_TYPE(clz_rel) == JEFF_REL_METHOD) {
              GEN_INSN (LDI4, fil, elm, NEW_REL
                        (METHOD, FIL, clz_rel, GET_FIL_OFFSET (uid)));
              insn1 = GEN_INSN (LDI4, lhs, fil, NEW_REL
                                (METHOD, CIL, clz_rel, GET_CIL_OFFSET (idx)));
            } else if (GET_REL_TYPE(clz_rel) ==  JEFF_REL_FIELD) {
              GEN_INSN (LDI4, fil, elm, NEW_REL
                        (FIELD, FIL, clz_rel, GET_FIL_OFFSET (uid)));
              insn1 = GEN_INSN (LDI4, lhs, fil, NEW_REL
                                (FIELD, CIL, clz_rel, GET_CIL_OFFSET (idx)));
            } else {
              GEN_INSN (LDI4, fil, elm, NEW_REL
                        (CLASS, FIL, clz_rel, GET_FIL_OFFSET (uid)));
              insn1 = GEN_INSN (LDI4, lhs, fil, NEW_REL
                                (CLASS, CIL, clz_rel, GET_CIL_OFFSET (idx)));

            }
          }
        else
          /* Otherwise, we must go the slow path.  */
#endif
          {
            if ((insn1 = GEN_INSN
                 (CALLNATIVE, lhs,
                  NEW_INTRINSIC (jeff_interp_classbase), 2)))
              {
                *(jit_insn_opndv (insn1, 2)) = cc->self_reg;
                *(jit_insn_opndv (insn1, 3)) = *(jit_insn_opnd (insn, 1));
              }

            GEN_INSN (CMP, cc->cmp_reg, lhs, NEW_CONST (I4, 0));
            GEN_INSN (BEQ, cc->cmp_reg, get_common_thrown_block (cc), 0);
          }
        break;
      }

    case JIT_OP_ARRAYLEN:
      {
        JitReg len = jit_cc_new_reg_I4 (cc);
        JitReg lhs = *(jit_insn_opnd (insn, 0));
        JitReg array = *(jit_insn_opnd (insn, 1));

        GEN_INSN (LDI4, len, array,
                  NEW_CONST (I4, offsetof (JeffArrayObject, length)));
        insn1 = GEN_INSN (SHRU, lhs, len,
                          NEW_CONST (I4, JEFF_ARRAY_LENGTH_SHIFT));
        break;
      }

    case JIT_OP_LDVTABLE:
      {
        JitReg clz = jit_cc_new_reg_I4 (cc);
        JitReg vtable = *(jit_insn_opnd (insn, 0));
        JitReg object = *(jit_insn_opnd (insn, 1));

        GEN_INSN (LDI4, clz, object,
                  NEW_CONST (I4, offsetof (JeffObject, header)));
#if BEIHAI_ENABLE_WEAK_REF != 0
        /* Set bit[0-1] with zero since it may be 1 for WeakReference Object */
        GEN_INSN (AND, clz, clz, NEW_CONST (I4, ~2));
#endif
        if ((insn1 = GEN_INSN
              (CALLNATIVE, vtable,
               NEW_INTRINSIC (jeff_get_vtable), 1))) {
          *(jit_insn_opndv (insn1, 2)) = clz;
        }

        break;
      }

    case JIT_OP_LDMETHOD:
      {
        JitReg method = *(jit_insn_opnd (insn, 0));
        JitReg vtable = *(jit_insn_opnd (insn, 1));
        JitReg index = *(jit_insn_opnd (insn, 2));
        unsigned index_rel = jit_cc_get_const_I4_rel (cc, index);
        unsigned offset = jit_cc_get_const_I4 (cc, index) * sizeof (void *);

        /* TODO : handle vtable for prelink */
        insn1 = GEN_INSN (LDI4, method, vtable,
                          NEW_REL (METHOD, MTDOFF, index_rel, offset));
        break;
      }

    case JIT_OP_CHKZERO:
      {
        JitReg exc_label;
        JitReg val = *(jit_insn_opnd (insn, 1));
        int val_kind = jit_reg_kind (val);

        exc_label = insert_exception_block (cc, insn, JIT_INTERP_ACTION_AE, 0);
        GEN_INSN (CMP, cc->cmp_reg, val, jit_reg_new_zero (val_kind));
        insn1 = GEN_INSN (BEQ, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_CHKNULL:
      {
        JitReg exc_label;

        exc_label = insert_exception_block (cc, insn, JIT_INTERP_ACTION_NPE, 0);
        GEN_INSN (CMP, cc->cmp_reg, *(jit_insn_opnd (insn, 1)), NEW_CONST (I4, 0));
        insn1 = GEN_INSN (BEQ, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_CHKARRIDX:
      {
        JitReg length = *(jit_insn_opnd (insn, 1));
        JitReg index = *(jit_insn_opnd (insn, 2));
        JitReg exc_label;

        exc_label = insert_exception_block (cc, insn, JIT_INTERP_ACTION_AIOOBE, 0);
        GEN_INSN (CMP, cc->cmp_reg, index, length);
        insn1 = GEN_INSN (BGEU, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_CHKARRVAL:
      {
        JitReg exc_label;
        JitReg result = jit_cc_new_reg_I4 (cc);

        exc_label = insert_exception_block (cc, insn, JIT_INTERP_ACTION_THROWN, 0);

        if ((insn1 = GEN_INSN
             (CALLNATIVE, result,
              NEW_INTRINSIC (jeff_interp_check_ase), 2)))
          {
            *(jit_insn_opndv (insn1, 2)) = *(jit_insn_opnd (insn, 1));
            *(jit_insn_opndv (insn1, 3)) = *(jit_insn_opnd (insn, 2));
          }

        GEN_INSN (CMP, cc->cmp_reg, result, NEW_CONST (I4, 0));
        insn1 = GEN_INSN (BNE, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_CHKCAST:
      {
        JitReg exc_label;
        JitReg result = jit_cc_new_reg_I4 (cc);

        exc_label = insert_exception_block (cc, insn, JIT_INTERP_ACTION_THROWN, 0);

        if ((insn1 = GEN_INSN
             (CALLNATIVE, result,
              NEW_INTRINSIC (jeff_interp_check_cce), 3)))
          {
            *(jit_insn_opndv (insn1, 2)) = *(jit_insn_opnd (insn, 1));
            *(jit_insn_opndv (insn1, 3)) = *(jit_insn_opnd (insn, 2));
            *(jit_insn_opndv (insn1, 4)) = *(jit_insn_opnd (insn, 3));
          }

        GEN_INSN (CMP, cc->cmp_reg, result, NEW_CONST (I4, 0));
        insn1 = GEN_INSN (BNE, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_CHKSOE:
      {
        JitReg top = *(jit_insn_opnd (insn, 1));
        JitReg boundary = *(jit_insn_opnd (insn, 2));
        JitReg exc_label;

        exc_label = insert_exception_block (cc, NULL, JIT_INTERP_ACTION_SOE, 0);
        GEN_INSN (CMP, cc->cmp_reg, top, boundary);
        insn1 = GEN_INSN (BGTU, cc->cmp_reg, exc_label, 0);
        break;
      }

    case JIT_OP_INVOKENATIVE:
      {
        JitReg exc = jit_cc_new_reg_I4 (cc);

        /* Convert it to a normal call without exception check.  */
        insn->opcode = JIT_OP_CALLNATIVE;
        insn = insn->next;
        GEN_INSN (LDI4, exc, cc->self_reg,
                  NEW_CONST (I4, offsetof (JeffThread, cur_exception)));
        GEN_INSN (CMP, cc->cmp_reg, exc, NEW_CONST (I4, 0));

        return GEN_INSN (BNE, cc->cmp_reg, get_common_thrown_block (cc), 0);
      }

    case JIT_OP_INVOKEMETHOD:
      {
        const JitReg result = *(jit_insn_opndv (insn, 0));
        const JitReg method = *(jit_insn_opndv (insn, 1));
        const unsigned opnd_num = jit_insn_opndv_num (insn);
        unsigned outs_off = cc->total_frame_size + jeff_interp_outs_offset (0);
        unsigned i;

        /* Generate code to pass arguments to the outs area.  */
        for (i = 2; i < opnd_num; i++)
          {
            JitReg arg = *(jit_insn_opndv (insn, i));

            switch (jit_reg_kind (arg))
              {
              case JIT_REG_KIND_I4:
                GEN_INSN (STI4, arg, cc->fp_reg, NEW_CONST (I4, outs_off));
                outs_off += 4;
                break;
              case JIT_REG_KIND_I8:
                GEN_INSN (STI8, arg, cc->fp_reg, NEW_CONST (I4, outs_off));
                outs_off += 8;
                break;
              case JIT_REG_KIND_F4:
                GEN_INSN (STF4, arg, cc->fp_reg, NEW_CONST (I4, outs_off));
                outs_off += 4;
                break;
              case JIT_REG_KIND_F8:
                GEN_INSN (STF8, arg, cc->fp_reg, NEW_CONST (I4, outs_off));
                outs_off += 8;
                break;
              default:
                jit_assert (0);
              }
          }

#if BEIHAI_ENABLE_JIT_LLVM == 0
        insn1 = GEN_INSN (CALLBC, result, 0, method);
#else
        {
          JitReg action = jit_cc_new_reg_I4 (cc);
          JitReg jit_info = jit_cc_new_reg_I4 (cc);
          JitReg jited_code = jit_cc_new_reg_I4 (cc);
          JeffMethodLinked *m;

          GEN_INSN (LDJITINFO, jit_info);
          GEN_INSN (STI4, cc->fp_reg, jit_info,
                    NEW_CONST (I4, offsetof (JitInterpSwitchInfo, frame)));
          if (jit_reg_is_const (method)
              && (m = (JeffMethodLinked*)jit_cc_get_const_I4 (cc, method))
              && m->jited_code != jit_globals.call_to_interp_from_jited)
            /* The method has already been jited. */
            jited_code = NEW_CONST (I4, (unsigned)m->jited_code);
          else
            {
              GEN_INSN (STI4, method, jit_info,
                        NEW_CONST (I4, offsetof (JitInterpSwitchInfo, out)));
              GEN_INSN (LDI4, jited_code, method,
                        NEW_CONST (I4, offsetof (JeffMethodLinked, jited_code)));
            }

          if ((insn1 = GEN_INSN (CALLNATIVE, action, jited_code, 2)))
            {
              *(jit_insn_opndv (insn1, 2)) = cc->self_reg;
              *(jit_insn_opndv (insn1, 3)) = jit_info;
            }

#if BEIHAI_ENABLE_JIT_BH_CODEGEN != 0
          /* Save to info.out.ret.last_return_type */
          GEN_INSN (STI4, action, jit_info, NEW_CONST (I4, 20));
#endif
          GEN_INSN (CMP, cc->cmp_reg, action, NEW_CONST (I4, JIT_INTERP_ACTION_RET_VOID));
          GEN_INSN (BLTS, cc->cmp_reg, get_leave_from_callbc_block (cc, action), 0);
          if (result)
            {
              GEN_INSN (LDJITINFO, jit_info);
              switch (jit_reg_kind (result))
                {
                  case JIT_REG_KIND_I4:
                    GEN_INSN (LDI4, result, jit_info, NEW_CONST (I4, 4));
                    break;
                  case JIT_REG_KIND_I8:
                    GEN_INSN (LDI8, result, jit_info, NEW_CONST (I4, 4));
                    break;
                  case JIT_REG_KIND_F4:
                    GEN_INSN (LDF4, result, jit_info, NEW_CONST (I4, 12));
                    break;
                  case JIT_REG_KIND_F8:
                    GEN_INSN (LDF8, result, jit_info, NEW_CONST (I4, 12));
                    break;
                  default:
                    jit_assert (0);
                    break;
                }
            }
        }

#endif
        break;
      }

    case JIT_OP_RETURN:
    case JIT_OP_ARETURN:
      {
        JitReg result = *(jit_insn_opnd (insn, 0));
        JitReg prev_frame = jit_cc_new_reg_I4 (cc);
        unsigned action = JIT_INTERP_ACTION_RET_VOID;

        GEN_INSN (LDI4, prev_frame, cc->fp_reg,
                  NEW_CONST (I4, offsetof (JeffInterpFrame, prev_frame)));

        switch (jit_reg_kind (result))
          {
          case JIT_REG_KIND_VOID:
            action = JIT_INTERP_ACTION_RET_VOID;
            break;
          case JIT_REG_KIND_I4:
            action = JIT_INTERP_ACTION_RET_I4;
            break;
          case JIT_REG_KIND_I8:
            action = JIT_INTERP_ACTION_RET_I8;
            break;
          case JIT_REG_KIND_F4:
            action = JIT_INTERP_ACTION_RET_F4;
            break;
          case JIT_REG_KIND_F8:
            action = JIT_INTERP_ACTION_RET_F8;
            break;
          default:
            jit_assert (0);
          }

        if (insn->opcode == JIT_OP_ARETURN)
          action = JIT_INTERP_ACTION_RET_REF;

        /* Free stack space of the current frame.  */
        GEN_INSN (STI4, cc->fp_reg, cc->self_reg,
                  NEW_CONST (I4, offsetof (JeffThread,
                                           java_stack.s.top)));
        /* Set the prev_frame as the current frame.  */
        GEN_INSN (STI4, prev_frame, cc->self_reg,
                  NEW_CONST (I4, offsetof (JeffThread, cur_frame)));
#if BEIHAI_ENABLE_JIT_LLVM == 0
        GEN_INSN (MOV, cc->fp_reg, prev_frame);
        insn1 = GEN_INSN (RETURNBC, NEW_CONST (I4, action), result, 0);
#else
        insn1 = GEN_INSN (RETURNBC, NEW_CONST (I4, action), result, 0, prev_frame);
#endif
        break;
      }

    default:
      return insn;
    }

  jit_insn_unlink (insn);
  jit_insn_delete (insn);

  return insn1;
}

bool
jit_frontend_jeff_lower (JitCompContext *cc)
{
  int label_index, end_label_index;
  JitBlock *block;
  JitInsn *insn;

  /* For saving the common THROWN leaving block.  */
  cc->pass_local_data = NULL;

  JIT_FOREACH_BLOCK_ENTRY_EXIT (cc, label_index, end_label_index, block)
    {
      JIT_FOREACH_INSN (block, insn)
        {
          if (!(insn = lower_one_insn (cc, block, insn)))
            return false;

          if (jit_get_error () == JIT_ERROR_OOM)
            return false;
        }
    }

  return true;
}

uint32
jit_frontend_jeff_aot_reloc_value_lower (const void *method, uint32 reloc_info)
{
  const JeffMethodLinked *m = (JeffMethodLinked *)method;
  const JeffClassHeaderLinked *c = jeff_get_method_class (m);
  const unsigned rel_type = GET_REL_TYPE (reloc_info);
  const unsigned rel_mod  = GET_REL_MOD (reloc_info);
  const unsigned rel_data = GET_REL_DATA (reloc_info);
  union
  {
    JeffClassHeaderLinked *c;
    JeffMethodLinked *m;
    JeffFieldLinked *f;
    uint32 val;
  } ret;

  switch (rel_type)
    {
    case JEFF_REL_BCIP:
      return (uint32)c + rel_data;

    case JEFF_REL_CLASS:
      {
        if (!rel_data)
          /* Get the current class.  */
          return (uint32)c;

        ret.c = jeff_get_class (c, rel_data, false);

        switch (rel_mod)
          {
          case JEFF_REL_MOD_NONE:
            return ret.val;

          case JEFF_REL_MOD_FIL:
            {
              uint16 uid = jeff_runtime_file_to_fuid (jeff_get_file_header (ret.c));
              return GET_FIL_OFFSET (uid);
            }

          case JEFF_REL_MOD_CIL:
            return GET_CIL_OFFSET (jeff_get_class_index
                                   (ret.c, ret.c->this_class_index));
          }

        break;
      }

    case JEFF_REL_METHOD:
      {
        JeffClassHeaderLinked *method_class;

        if (!rel_data)
          /* Get the current method.  */
          return (uint32)m;

        ret.m = jeff_get_resolved_method (c, rel_data, false);
        method_class = jeff_get_method_class (ret.m);

        switch (rel_mod)
          {
          case JEFF_REL_MOD_NONE:
            return ret.val;

          case JEFF_REL_MOD_CLASS:
            return (uint32)jeff_get_method_class (ret.m);

          case JEFF_REL_MOD_MTDIDX:
            if ((method_class->access_flag & JEFF_ACC_INTERFACE))
              break;
            else
              return jeff_get_method_vtable_index (ret.m);

          case JEFF_REL_MOD_MTDOFF:
            if ((method_class->access_flag & JEFF_ACC_INTERFACE))
              break;
            else
              return (/*offsetof (JeffClassExtra, vtable)*/ 0
                      + jeff_get_method_vtable_index (ret.m) * sizeof (void *));

          case JEFF_REL_MOD_SPEMTD:
            {
              if ((c->access_flag & JEFF_ACC_SUPER)
                  && method_class != c
                  && !(ret.m->access_flag & JEFF_ACC_INIT))
                ret.m = jeff_select_method_virtual
                  (jeff_get_super_class (c), ret.m);

              return ret.val;
            }

          case JEFF_REL_MOD_FIL:
            {
              uint16 uid = jeff_runtime_file_to_fuid (jeff_get_file_header (method_class));
              return GET_FIL_OFFSET (uid);
            }

          case JEFF_REL_MOD_CIL:
            return GET_CIL_OFFSET (jeff_get_class_index
                                   (method_class, method_class->this_class_index));
          }

        break;
      }

    case JEFF_REL_FIELD:
      {
        JeffClassHeaderLinked *field_class;
        ret.f = jeff_get_resolved_field (c, rel_data, false);
        field_class = jeff_get_field_class (ret.f);

        switch (rel_mod)
          {
          case JEFF_REL_MOD_NONE:
            return ret.val;

          case JEFF_REL_MOD_CLASS:
            return (uint32)jeff_get_field_class (ret.f);

          case JEFF_REL_MOD_FLDOFF:
            return (((ret.f->access_flag & JEFF_ACC_STATIC)
                     ? offsetof (JeffClassInstanceLocal, static_area)
                     : 0) + jeff_get_field_data_offset (ret.f));

          case JEFF_REL_MOD_FIL:
            {
              uint16 uid = jeff_runtime_file_to_fuid (jeff_get_file_header (field_class));
              return GET_FIL_OFFSET (uid);
            }

          case JEFF_REL_MOD_CIL:
            return GET_CIL_OFFSET (jeff_get_class_index
                                   (field_class, field_class->this_class_index));
          }

        break;
      }

    case JEFF_REL_INTRINSIC:
      {
        switch (rel_data)
          {
#define INTRINSIC(NAME)                             \
            case JIT_FRONTEND_JEFF_INTRINSIC_##NAME:  \
              return (uint32)NAME;
#include "jit-frontend-jeff-intrinsic.def"
#undef INTRINSIC
          }
        break;
      }
    case JIT_REL_CG_INTRINSIC:
      {
        switch (rel_data)
        {
#define INTRINSIC(NAME) \
            case JIT_CG_INTRINSIC_##NAME:  \
              return (uint32)NAME;
#include "../../cg/jit-cg-intrinsic.def"
#undef INTRINSIC
        }
      }
    }

  jit_set_error (JIT_ERROR_UNSUPPORTED_RELOC);

  return 0;
}
