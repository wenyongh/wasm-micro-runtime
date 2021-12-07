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
 * @file   jit-frontend-jeff.c
 * @author Jiutao <jiu-tao.nie@intel.com>
 * @date   Fri Mar 15 14:40:56 2013
 *
 * @brief  JEFF front end
 */

#include "../../../vmcore_jeff/jeff-runtime.h"
#include "../../../vmcore_jeff/jeff-thread.h"
#include "../../../vmcore_jeff/jeff-sync.h"
#include "../../../vmcore_jeff/jeff-opcode.h"
#include "../../../vmcore_jeff/jeff-interp.h"
#include "jeff-export.h"

#include "jit-profiler.h"
#include "jit-region.h"
#include "jit-frontend.h"
#include "jit-frontend-jeff.h"

#ifdef BH_VXWORKS
#undef NONE
#endif

void*
jit_frontend_jeff_cur_method_and_sp (uint32 *sp)
{
  JeffThread *self = jeff_runtime_get_self ();
  JeffInterpFrame *f = (JeffInterpFrame *)jeff_thread_get_cur_frame (self);
  *sp = f->sp - f->lp;
  return f->method;
}

/* *
 * Get method of the given Frame */
void*
jit_frontend_jeff_get_method_of_frame (void* frame) {
  JeffMethodLinked *method = NULL;
  if (frame != NULL) {
    method = ((JeffInterpFrame*)(frame))->method;
  }
  return (void*)method;
}

/* Record information of a value slot of local variable or stack
   during translation.  */
typedef struct ValueSlot
{
  /* The virtual register that holds the value of the slot if the
     value of the slot is in register.  */
  JitReg reg;

  /* The dirty bit of the value slot.  It's set if the value in
     register is newer than the value in memory.  */
  unsigned dirty : 1;

  /* Whether the new value in register is a reference, which is valid
     only when the dirty bit is set.  */
  unsigned ref : 1;

  /* Committed reference flag.  0: unknown, 1: not-reference, 2:
     reference.  */
  unsigned committed_ref : 2;
} ValueSlot;

/* Frame information for translation.  */
typedef struct Frame
{
  /* The current method pointer.  */
  JeffMethodLinked *cur_method;

  /* The current class pointer.  */
  JeffClassHeaderLinked *cur_class;

  /* Local slot number.  */
  unsigned max_locals;

  /* Operand stack slot number.  */
  unsigned max_stack;

  /* The current compilation context.  */
  JitCompContext *cc;

  /* The current basic block.  */
  JitBlock *block;

  /* Instruction pointer */
  uint8  *ip;

  /* Stack top pointer */
  ValueSlot *sp;

  /* Committed instruction pointer */
  uint8  *committed_ip;

  /* Committed stack top pointer */
  ValueSlot *committed_sp;

  /* Local variables */
  ValueSlot lp[1];
} Frame;


/**
 * Helper function for GEN_INSN
 *
 * @param cc compilation context
 * @param block the current block
 * @param insn the new instruction
 *
 * @return the new instruction if inserted, NULL otherwise
 */
static inline JitInsn*
_gen_insn (JitCompContext *cc, JitBlock *block, JitInsn *insn)
{
  if (insn)
    jit_block_append_insn (block, insn);

  return insn;
}

/**
 * Generate and append an instruction to the current block.
 */
#define GEN_INSN(...)                                       \
  _gen_insn (cc, block, jit_cc_new_insn (cc, __VA_ARGS__))

/**
 * Helper function for GEN_INSN_NORM_1
 *
 * @param cc compilation context
 * @param block the current block
 * @param kind kind fo the result register
 * @param result points to the returned result register
 * @param insn the instruction
 *
 * @return the new instruction if inserted, NULL otherwise
 */
static JitInsn*
_gen_insn_norm_1 (JitCompContext *cc, JitBlock *block,
                  unsigned kind, JitReg *result, JitInsn *insn)
{
  if (!*result && insn)
    {
      JitRegVec vec = jit_insn_opnd_regs (insn);
      JitReg *lhs = jit_reg_vec_at (&vec, 0);

      if (!*lhs)
        *lhs = jit_cc_new_reg (cc, kind);

      *result = *lhs;
      jit_block_append_insn (block, insn);
      *(jit_annr_def_insn (cc, *lhs)) = insn;

      return insn;
    }

  return NULL;
}

/**
 * Helper macro for GEN_INSN_NORM
 */
#define GEN_INSN_NORM_1(Kind, result, ...)                              \
  _gen_insn_norm_1 (cc, block, Kind, &result,                           \
                    jit_cc_new_insn_norm (cc, &result, __VA_ARGS__))

/**
 * Generate and append a normalized instruction to the current block.
 *
 * @param Type type of the result
 * @param result result of the normalized instruction
 */
#define GEN_INSN_NORM(Type, result, ...)                        \
  GEN_INSN_NORM_1 (JIT_REG_KIND_##Type, result, __VA_ARGS__)

static void
gen_commit_for_exception (Frame *frame);

#if 0
static void
gen_commit_ip (Frame *frame);
#endif

#define FRAME_IP() NEW_REL (BCIP, NONE, offset_of_addr (frame, frame->ip), frame->ip)

/**
 * Helper function for GEN_INSN_CHK.
 */
static void
_gen_insn_chk (Frame *frame, JitReg *result, JitInsn *insn,
               JeffClassHeaderLinked *ec)
{
  if (!*result && insn)
    {
      JeffMethodLinked *method = (JeffMethodLinked *)frame->cc->method;
      JeffVarOffset bc_ip = jit_cc_get_const_I4 (frame->cc,
                                                 *(jit_insn_opnd (insn, 0)));

      /* Should commit frame ip to print the stack trace of exception. */
      /*gen_commit_ip (frame);*/ /* frame ip is committed only before exception is thrown */
      if (jeff_find_exception_handler (method, bc_ip, ec))
        /* Only generate commit if the exception can be caught by the
           current method.  */
        gen_commit_for_exception (frame);

      jit_block_append_insn (frame->block, insn);
    }
}

#define DEF_GET_CLASS_FOR(OPNAME, CLZNAME)          \
  static JeffClassHeaderLinked*                     \
  get_class_for_##OPNAME ()                         \
  {                                                 \
    static JeffClassHeaderLinked *ec = NULL;        \
    if (!ec)                                        \
      ec = jeff_runtime_class_for_name (CLZNAME);   \
    return ec;                                      \
  }

DEF_GET_CLASS_FOR (CHKZERO,   "java.lang.ArithmeticException")
DEF_GET_CLASS_FOR (CHKNULL,   "java.lang.NullPointerException")
DEF_GET_CLASS_FOR (CHKARRIDX, "java.lang.ArrayIndexOutOfBoundsException")
DEF_GET_CLASS_FOR (CHKARRVAL, "java.lang.ArrayStoreException")
DEF_GET_CLASS_FOR (CHKCAST,   "java.lang.ClassCastException")

/**
 * Generate and append a check instruction to the current block.
 */
#define GEN_INSN_CHK(NAME, ...) do {                            \
    JitReg _result;                                             \
    _gen_insn_chk (frame, &_result,                             \
                   jit_cc_new_insn_norm (cc, &_result,          \
                                         NAME, __VA_ARGS__),    \
                   get_class_for_##NAME ());                    \
  } while (0)


/********************************************************************
 *      Stack and local variable array accessing operations
 ********************************************************************/

/**
 * Get the offset from frame pointer to the n-th local variable slot.
 *
 * @param n the index to the local variable array
 *
 * @return the offset from frame pointer to the local variable slot
 */
static inline unsigned
offset_of_local (unsigned n)
{
  return offsetof (JeffInterpFrame, lp) + n * 4;
}

/**
 * Get the offset from frame pointer to the n-th local variable's
 * reference flag slot.
 *
 * @param frame the frame information
 * @param n the index to the local variable array
 *
 * @return the offset from frame pointer to the local variable slot
 */
static inline unsigned
offset_of_ref (Frame *frame, unsigned n)
{
  return offset_of_local (frame->max_locals + frame->max_stack) + n;
}

/**
 * Get the offset in class of the given address
 *
 * @param frame the frame information
 * @param addr address in the loaded file
 *
 * @return
 */
static inline unsigned
offset_of_addr (Frame *frame, void *addr)
{
  return (uint8 *)addr - (uint8 *)frame->cur_class;
}

/**
 * Generate instruction to load an integer from the frame.
 *
 * This and the below gen_load_X functions generate instructions to
 * load values from the frame into registers if the values have not
 * been loaded yet.
 *
 * @param frame the frame information
 * @param n slot index to the local variable array
 *
 * @return register holding the loaded value
 */
static JitReg
gen_load_i (Frame *frame, unsigned n)
{
  if (!frame->lp[n].reg)
    {
      JitCompContext *cc = frame->cc;
      JitBlock *block = frame->block;
      frame->lp[n].reg = jit_cc_new_reg_I4 (cc);
      GEN_INSN (LDI4, frame->lp[n].reg, cc->fp_reg,
                NEW_CONST (I4, offset_of_local (n)));
    }

  return frame->lp[n].reg;
}

static JitReg
gen_load_r (Frame *frame, unsigned n)
{
  if (!frame->lp[n].reg)
    {
      JitCompContext *cc = frame->cc;
      JitBlock *block = frame->block;
      frame->lp[n].reg = jit_cc_new_reg_I4 (cc);
      GEN_INSN (LDI4, frame->lp[n].reg, cc->fp_reg,
                NEW_CONST (I4, offset_of_local (n)));
    }

  return frame->lp[n].reg;
}

/**
 * Generate instruction to load a floating point value from the frame.
 *
 * @param frame the frame information
 * @param n slot index to the local variable array
 *
 * @return register holding the loaded value
 */
static JitReg
gen_load_f (Frame *frame, unsigned n)
{
  if (!frame->lp[n].reg)
    {
      JitCompContext *cc = frame->cc;
      JitBlock *block = frame->block;
      frame->lp[n].reg = jit_cc_new_reg_F4 (cc);
      GEN_INSN (LDF4, frame->lp[n].reg, cc->fp_reg,
                NEW_CONST (I4, offset_of_local (n)));
    }

  return frame->lp[n].reg;
}

/**
 * Generate instruction to load a long integer from the frame.
 *
 * @param frame the frame information
 * @param n slot index to the local variable array
 *
 * @return register holding the loaded value
 */
static JitReg
gen_load_l (Frame *frame, unsigned n)
{
  if (!frame->lp[n].reg)
    {
      JitCompContext *cc = frame->cc;
      JitBlock *block = frame->block;
      frame->lp[n].reg = frame->lp[n + 1].reg = jit_cc_new_reg_I8 (cc);
      GEN_INSN (LDI8, frame->lp[n].reg, cc->fp_reg,
                NEW_CONST (I4, offset_of_local (n)));
    }

  return frame->lp[n].reg;
}

/**
 * Generate instruction to load a double value from the frame.
 *
 * @param frame the frame information
 * @param n slot index to the local variable array
 *
 * @return register holding the loaded value
 */
static JitReg
gen_load_d (Frame *frame, unsigned n)
{
  if (!frame->lp[n].reg)
    {
      JitCompContext *cc = frame->cc;
      JitBlock *block = frame->block;
      frame->lp[n].reg = frame->lp[n + 1].reg = jit_cc_new_reg_F8 (cc);
      GEN_INSN (LDF8, frame->lp[n].reg, cc->fp_reg,
                NEW_CONST (I4, offset_of_local (n)));
    }

  return frame->lp[n].reg;
}

/**
 * Generate instructions to commit computation result to the frame.
 * The general principle is to only commit values that will be used
 * through the frame.
 *
 * @param frame the frame information
 * @param begin the begin value slot to commit
 * @param end the end value slot to commit
 * @param only_ref_for_stack if it's true, only store slots of working
 * stack whose reference flags are changed or that are reference types
 */
static void
gen_commit_values (Frame *frame, ValueSlot *begin, ValueSlot *end,
                   bool only_ref_for_stack)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;
  ValueSlot *p;
  int n;

  for (p = begin; p < end; p++)
    {
      if (!p->dirty
          || (only_ref_for_stack
              && p >= frame->lp + frame->max_locals
              && !p->ref && p->ref == p->committed_ref - 1))
        continue;

      p->dirty = 0;
      n = p - frame->lp;

      if (p->ref != p->committed_ref - 1)
        /* Commit reference flag.  */
        switch (jit_reg_kind (p->reg))
          {
          case JIT_REG_KIND_I4:
          case JIT_REG_KIND_F4:
            GEN_INSN (STI1, NEW_CONST (I4, p->ref), cc->fp_reg,
                      NEW_CONST (I4, offset_of_ref (frame, n)));
            p->committed_ref = 1 + p->ref;
            break;
          case JIT_REG_KIND_I8:
          case JIT_REG_KIND_F8:
            GEN_INSN (STI2, NEW_CONST (I4, p->ref | (p->ref << 8)), cc->fp_reg,
                      NEW_CONST (I4, offset_of_ref (frame, n)));
            p->committed_ref = (p + 1)->committed_ref = 1 + p->ref;
            break;
          default:
            jit_assert (0);
          }

      switch (jit_reg_kind (p->reg))
        {
        case JIT_REG_KIND_I4:
          GEN_INSN (STI4, p->reg, cc->fp_reg,
                    NEW_CONST (I4, offset_of_local (n)));
          break;

        case JIT_REG_KIND_I8:
          GEN_INSN (STI8, p->reg, cc->fp_reg,
                    NEW_CONST (I4, offset_of_local (n)));
          (++p)->dirty = 0;
          break;

        case JIT_REG_KIND_F4:
          GEN_INSN (STF4, p->reg, cc->fp_reg,
                    NEW_CONST (I4, offset_of_local (n)));
          break;

        case JIT_REG_KIND_F8:
          GEN_INSN (STF8, p->reg, cc->fp_reg,
                    NEW_CONST (I4, offset_of_local (n)));
          (++p)->dirty = 0;
          break;
        }
    }

  /* Clear reference flags for unused stack slots.  */
  for (p = frame->sp, end = frame->lp + frame->max_locals + frame->max_stack;
       p < end; p++)
    {
      jit_assert (!p->ref);
      n = p - frame->lp;

      if (p->ref != p->committed_ref - 1)
        /* Commit reference flag.  */
        {
          GEN_INSN (STI1, NEW_CONST (I4, p->ref), cc->fp_reg,
                    NEW_CONST (I4, offset_of_ref (frame, n)));
          p->committed_ref = 1 + p->ref;
        }
    }
}

/**
 * Generate instructions to commit SP and IP pointers to the frame.
 *
 * @param frame the frame information
 */
static void
gen_commit_sp_ip (Frame *frame)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;
  JitReg sp;

  if (frame->sp != frame->committed_sp)
    {
      GEN_INSN_NORM (I4, sp, ADD, 0, cc->fp_reg,
                     NEW_CONST (I4, offset_of_local (frame->sp - frame->lp)));
      GEN_INSN (STI4, sp, cc->fp_reg,
                NEW_CONST (I4, offsetof (JeffInterpFrame, sp)));
      frame->committed_sp = frame->sp;
    }

  if (frame->ip != frame->committed_ip)
    {
      GEN_INSN (STI4,
                NEW_REL (BCIP, NONE, offset_of_addr (frame, frame->ip), frame->ip),
                cc->fp_reg,
                NEW_CONST (I4, offsetof (JeffInterpFrame, ip)));
      frame->committed_ip = frame->ip;
    }
}

/**
 * Generate instructions to commit IP pointer to the frame.
 *
 * @param frame the frame information
 */
#if 0
static void
gen_commit_ip (Frame *frame)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;

  if (frame->ip != frame->committed_ip)
    {
      GEN_INSN (STI4,
                NEW_REL (BCIP, NONE, offset_of_addr (frame, frame->ip), frame->ip),
                cc->fp_reg,
                NEW_CONST (I4, offsetof (JeffInterpFrame, ip)));
      frame->committed_ip = frame->ip;
  }
}
#endif

/**
 * Generate commit instructions for the block end.
 *
 * @param frame the frame information
 */
static inline void
gen_commit_for_branch (Frame *frame)
{
  gen_commit_values (frame, frame->lp, frame->sp, false);
}

/**
 * Generate commit instructions for exception checks.
 *
 * @param frame the frame information
 */
static inline void
gen_commit_for_exception (Frame *frame)
{
  gen_commit_values (frame, frame->lp, frame->lp + frame->max_locals, false);
}

/**
 * Generate commit instructions for operations that may cause GC
 * exceptions.
 *
 * @param frame the frame information
 */
static inline void
gen_commit_for_gc (Frame *frame)
{
  gen_commit_values (frame, frame->lp, frame->sp, true);
  gen_commit_sp_ip (frame);
}

/**
 * Generate commit instructions to commit all status.
 *
 * @param frame the frame information
 */
static inline void
gen_commit_for_all (Frame *frame)
{
  gen_commit_values (frame, frame->lp, frame->sp, false);
  gen_commit_sp_ip (frame);
}

static void
push_i (Frame *frame, JitReg value)
{
  frame->sp->reg = value;
  frame->sp->dirty = 1;
  frame->sp++;
}

static void
push_r(Frame *frame, JitReg value)
{
  frame->sp->reg = value;
  frame->sp->dirty = 1;
  frame->sp->ref = 1;
  frame->sp++;
}

static inline void
push_f (Frame *frame, JitReg value)
{
  push_i (frame, value);
}

static void
push_l (Frame *frame, JitReg value)
{
  frame->sp->reg = value;
  frame->sp->dirty = 1;
  frame->sp++;
  frame->sp->reg = value;
  frame->sp->dirty = 1;
  frame->sp++;
}

static inline void
push_d (Frame *frame, JitReg value)
{
  push_l (frame, value);
}

static inline JitReg
pop_i (Frame *frame)
{
  frame->sp--;
  return gen_load_i (frame, frame->sp - frame->lp);
}

static inline JitReg
pop_r (Frame *frame)
{
  frame->sp--;
  frame->sp->ref = 0;
  return gen_load_r (frame, frame->sp - frame->lp);
}

static inline JitReg
pop_f (Frame *frame)
{
  frame->sp--;
  return gen_load_f (frame, frame->sp - frame->lp);
}

static inline JitReg
pop_l (Frame *frame)
{
  frame->sp -= 2;
  return gen_load_l (frame, frame->sp - frame->lp);
}

static inline JitReg
pop_d (Frame *frame)
{
  frame->sp -= 2;
  return gen_load_d (frame, frame->sp - frame->lp);
}

static inline void
pop (Frame *frame, int n)
{
  frame->sp -= n;
  memset (frame->sp, 0, n * sizeof (*frame->sp));
}

static inline JitReg
stack_r (Frame *frame, int n)
{
  return gen_load_r (frame, (frame->sp - n) - frame->lp);
}

static inline JitReg
local_i (Frame *frame, int n)
{
  return gen_load_i (frame, n);
}

static inline JitReg
local_r (Frame *frame, int n)
{
  return gen_load_r (frame, n);
}

static inline JitReg
local_f (Frame *frame, int n)
{
  return gen_load_f (frame, n);
}

static inline JitReg
local_l (Frame *frame, int n)
{
  return gen_load_l (frame, n);
}

static inline JitReg
local_d (Frame *frame, int n)
{
  return gen_load_d (frame, n);
}

static void
set_local_i (Frame *frame, int n,  JitReg val)
{
  frame->lp[n].reg = val;
  frame->lp[n].dirty = 1;
  frame->lp[n].ref = 0;
}

/* Pop the object reference or returnAddress from the top of the stack
   and store it into the local variable.  Since we don't support jsr
   instruction, the stored value cannot be returnAddress type, so we
   can set frame_ref[n] to 1 instead of *FRAME_REF (frame->sp - 1).  */

static void
store_local_r (Frame *frame, int n)
{
  frame->lp[n].reg = pop_r (frame);
  frame->lp[n].dirty = 1;
  frame->lp[n].ref = 1;
}

static inline void
set_local_f (Frame *frame, int n,  JitReg val)
{
  set_local_i (frame, n, val);
}

static void
set_local_l (Frame *frame, int n,  JitReg val)
{
  frame->lp[n].reg = val;
  frame->lp[n].dirty = 1;
  frame->lp[n].ref = 0;
  frame->lp[n + 1].reg = val;
  frame->lp[n + 1].dirty = 1;
  frame->lp[n + 1].ref = 0;
}

static inline void
set_local_d (Frame *frame, int n,  JitReg val)
{
  set_local_l (frame, n, val);
}

#define PUSH_I(value)       push_i (frame, value)
#define PUSH_R(value)       push_r (frame, value)
#define PUSH_L(value)       push_l (frame, value)
#define PUSH_F(value)       push_f (frame, value)
#define PUSH_D(value)       push_d (frame, value)
#define POP_I()             pop_i (frame)
#define POP_R()             pop_r (frame)
#define POP_L()             pop_l (frame)
#define POP_F()             pop_f (frame)
#define POP_D()             pop_d (frame)
#define POP(n)              pop (frame, n)
#define STACK_R(n)          stack_r (frame, n)
#define LOCAL_I(n)          local_i (frame, n)
#define LOCAL_R(n)          local_r (frame, n)
#define LOCAL_F(n)          local_f (frame, n)
#define LOCAL_L(n)          local_l (frame, n)
#define LOCAL_D(n)          local_d (frame, n)
#define SET_LOCAL_I(n, val) set_local_i (frame, n, val)
#define STORE_LOCAL_R(n)    store_local_r (frame, n)
#define SET_LOCAL_F(n, val) set_local_f (frame, n, val)
#define SET_LOCAL_L(n, val) set_local_l (frame, n, val)
#define SET_LOCAL_D(n, val) set_local_d (frame, n, val)


/********************************************************************
 *              Macros and functions for opcodes
 ********************************************************************/

/**
 * Shift bits of index to arrays of various types.
 */
#define SIZE_I1     1
#define SIZE_I2     2
#define SIZE_U2     2
#define SIZE_I4     4
#define SIZE_I8     8
#define SIZE_F4     4
#define SIZE_F8     8

/* Types corresponding to cell types: I, L, F, D.  */

typedef int32       CellType_I;
typedef int64       CellType_L;
typedef float       CellType_F;
typedef double      CellType_D;

#define JitType_I   JIT_REG_KIND_I4
#define JitType_L   JIT_REG_KIND_I8
#define JitType_F   JIT_REG_KIND_F4
#define JitType_D   JIT_REG_KIND_F8


/**
 * Put the value on top of the given frame's stack to the given
 * address and pop that value from the stack.
 *
 * @param addr register of field address
 * @param field_type the field type
 * @param off offset of the field
 * @param field_rel_off offset for relocation info if nonzero
 */
static void
PUT_FIELD (Frame *frame, JitReg addr, JeffType field_type, int off,
           unsigned field_rel_off)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;
  JitReg offreg = (field_rel_off
                   ? NEW_REL (FIELD, FLDOFF, field_rel_off, off)
                   : NEW_CONST (I4, off));

  if ((field_type & JEFF_TYPE_REF))
    GEN_INSN (STI4, pop_r (frame), addr, offreg);
  else
    switch (jeff_type_base (field_type))
      {
      case JEFF_TYPE_SHORT:
        GEN_INSN (STI2, POP_I (), addr, offreg);
        break;
      case JEFF_TYPE_INT:
        GEN_INSN (STI4, POP_I (), addr, offreg);
        break;
      case JEFF_TYPE_LONG:
        GEN_INSN (STI8, POP_L (), addr, offreg);
        break;
      case JEFF_TYPE_BYTE:
        GEN_INSN (STI1, POP_I (), addr, offreg);
        break;
      case JEFF_TYPE_CHAR:
        GEN_INSN (STI2, POP_I (), addr, offreg);
        break;
      case JEFF_TYPE_FLOAT:
        GEN_INSN (STF4, POP_F (), addr, offreg);
        break;
      case JEFF_TYPE_DOUBLE:
        GEN_INSN (STF8, POP_D (), addr, offreg);
        break;
      case JEFF_TYPE_BOOLEAN:
        GEN_INSN (STI1, POP_I (), addr, offreg);
        break;
      default:
        jit_assert (0);
      }
}

/**
 * Get the value from the given address and push it onto the top of
 * the given frame's stack.
 *
 * @param addr register of field address
 * @param field_type the field type
 * @param off offset of the field
 * @param field_rel_off offset for relocation info if nonzero
 */
static void
GET_FIELD (Frame *frame, JitReg addr, JeffType field_type, int off,
           unsigned field_rel_off)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;
  JitReg offreg = (field_rel_off
                   ? NEW_REL (FIELD, FLDOFF, field_rel_off, off)
                   : NEW_CONST (I4, off));

  if ((field_type & JEFF_TYPE_REF))
    {
      JitReg val = jit_cc_new_reg_I4 (cc);
      GEN_INSN (LDI4, val, addr, offreg);
      PUSH_R (val);
    }
  else
    switch (jeff_type_base (field_type))
      {
      case JEFF_TYPE_SHORT:
        {
          JitReg val = jit_cc_new_reg_I4 (cc);
          GEN_INSN (LDI2, val, addr, offreg);
          PUSH_I (val);
          break;
        }
      case JEFF_TYPE_INT:
        {
          JitReg val = jit_cc_new_reg_I4 (cc);
          GEN_INSN (LDI4, val, addr, offreg);
          PUSH_I (val);
          break;
        }
      case JEFF_TYPE_LONG:
        {
          JitReg val = jit_cc_new_reg_I8 (cc);
          GEN_INSN (LDI8, val, addr, offreg);
          PUSH_L (val);
          break;
        }
      case JEFF_TYPE_BYTE:
        {
          JitReg val = jit_cc_new_reg_I4 (cc);
          GEN_INSN (LDI1, val, addr, offreg);
          PUSH_I (val);
          break;
        }
      case JEFF_TYPE_CHAR:
        {
          JitReg val = jit_cc_new_reg_I4 (cc);
          GEN_INSN (LDU2, val, addr, offreg);
          PUSH_I (val);
          break;
        }
      case JEFF_TYPE_FLOAT:
        {
          JitReg val = jit_cc_new_reg_F4 (cc);
          GEN_INSN (LDF4, val, addr, offreg);
          PUSH_F (val);
          break;
        }
      case JEFF_TYPE_DOUBLE:
        {
          JitReg val = jit_cc_new_reg_F8 (cc);
          GEN_INSN (LDF8, val, addr, offreg);
          PUSH_D (val);
          break;
        }
      case JEFF_TYPE_BOOLEAN:
        {
          JitReg val = jit_cc_new_reg_I4 (cc);
          GEN_INSN (LDU1, val, addr, offreg);
          PUSH_I (val);
          break;
        }
      default:
        jit_assert (0);
      }
}

#define UNSUPPORTED_OPCODE() do {               \
    jit_assert (0);                             \
  } while (0)

#define CUR_IP_OFFSET() NEW_CONST (I4, offset_of_addr (frame, orig_ip - 1))

static JitReg
gen_array_addr (Frame *frame, JitReg array, JitReg index,
                JitReg ip_offset, int size, JitReg *offset)
{
  JitCompContext *cc = frame->cc;
  JitBlock *block = frame->block;
  JitReg base, length;
  uint32 index_const = 0;

  GEN_INSN_CHK (CHKNULL, ip_offset, array, FRAME_IP ());
  GEN_INSN_NORM (I4, length, ARRAYLEN, 0, array);
  GEN_INSN_CHK (CHKARRIDX, ip_offset, length, index, FRAME_IP ());

  if (jit_reg_is_const (index))
    {
      index_const = jit_cc_get_const_I4 (cc, index);
      base = array;
    }
  else
    {
      JitInsn *insn = *(jit_annr_def_insn (cc, index));

      if (insn && insn->opcode == JIT_OP_ADD)
        {
          JitReg opnd1 = *(jit_insn_opnd (insn, 1));
          JitReg opnd2 = *(jit_insn_opnd (insn, 2));

          /* (reg +/- const) and (const + reg) must be normalized to
             (reg + (+/-const)).  */
          if (jit_reg_is_const (opnd2))
            {
              index_const = jit_cc_get_const_I4 (cc, opnd2);
              index = opnd1;
            }
        }

      if (size > 1)
        GEN_INSN_NORM (I4, base, MUL, 0, index, NEW_CONST (I4, size));
      else
        base = index;

      GEN_INSN_NORM (I4, base, ADD, 0, array, base);
    }

  *offset = NEW_CONST
    (I4, (uint32)jeff_array_first_elem_addr (NULL) + index_const * size);

  return base;
}

#define DEF_OPCODE_XALOAD(ElemType, ResType, PushType) do {     \
    JitReg index = POP_I ();                                    \
    JitReg array = POP_R ();                                    \
    JitReg offset;                                              \
    JitReg base = gen_array_addr (frame, array, index,          \
                                  CUR_IP_OFFSET (),             \
                                  SIZE_##ElemType, &offset);    \
    JitReg result = jit_cc_new_reg_##ResType (cc);              \
      GEN_INSN (LD##ElemType, result, base, offset);            \
      PUSH_##PushType (result);                                 \
  } while (0)

#define DEF_OPCODE_XASTORE(ElemType, PopType) do {              \
    JitReg value = POP_##PopType ();                            \
    JitReg index = POP_I ();                                    \
    JitReg array = POP_R ();                                    \
    JitReg offset;                                              \
    JitReg base = gen_array_addr (frame, array, index,          \
                                  CUR_IP_OFFSET (),             \
                                  SIZE_##ElemType, &offset);    \
    GEN_INSN (ST##ElemType, value, base, offset);               \
  } while (0)

#define DEF_OPCODE_MATH_UNARY(OpPop, ResPush, Op) do {          \
    JitReg opnd = POP_##OpPop ();                               \
    JitReg result;                                              \
    GEN_INSN_NORM_1 (JitType_##ResPush, result, Op, 0, opnd);   \
    PUSH_##ResPush (result);                                    \
  } while (0)

#define DEF_OPCODE_MATH_BINARY(Op1Pop, Op2Pop, ResPush, Op) do {\
    JitReg opnd2 = POP_##Op2Pop ();                             \
    JitReg opnd1 = POP_##Op1Pop ();                             \
    JitReg result;                                              \
    GEN_INSN_NORM_1 (JitType_##ResPush, result, Op, 0,          \
                     opnd1, opnd2);                             \
    PUSH_##ResPush (result);                                    \
  } while (0)

#define DEF_OPCODE_MATH_DIV_REM(Type, OpndType, Op) do {        \
    JitReg opnd2 = POP_##Type ();                               \
    JitReg opnd1 = POP_##Type ();                               \
    JitReg result;                                              \
    GEN_INSN_CHK (CHKZERO, CUR_IP_OFFSET (), opnd2, FRAME_IP());\
    GEN_INSN_NORM (OpndType, result, Op, 0, opnd1, opnd2);      \
    PUSH_##Type (result);                                       \
  } while (0)

#define DEF_OPCODE_IF(Op) do {                              \
    JeffOffset offset = read_uint16_align (frame->ip);      \
    JitReg val = POP_I ();                                  \
    int taken = (uint8 *)cur_class + offset - orig_ip;      \
    int fall_through = frame->ip - orig_ip;                 \
                                                            \
    gen_commit_for_branch (frame);                          \
    GEN_INSN (CMP, cc->cmp_reg, val, NEW_CONST (I4, 0));    \
    GEN_INSN (Op, cc->cmp_reg,                              \
              NEW_CONST (I4, taken),                        \
              NEW_CONST (I4, fall_through));                \
    goto cleanup_and_return;                                \
  } while (0)

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
#define DEF_OPCODE_IF_W(Op) do {                            \
    JeffDOffset offset = read_uint32_align (frame->ip);     \
    JitReg val = POP_I ();                                  \
    int taken = (uint8 *)cur_class + offset - orig_ip;      \
    int fall_through = frame->ip - orig_ip;                 \
                                                            \
    gen_commit_for_branch (frame);                          \
    GEN_INSN (CMP, cc->cmp_reg, val, NEW_CONST (I4, 0));    \
    GEN_INSN (Op, cc->cmp_reg,                              \
              NEW_CONST (I4, taken),                        \
              NEW_CONST (I4, fall_through));                \
    goto cleanup_and_return;                                \
  } while (0)
#endif /* end of BEIHAI_ENABLE_JEFF_EXTENSION */

#define DEF_OPCODE_IFA(Op) do {                             \
    JeffOffset offset = read_uint16_align (frame->ip);      \
    JitReg val = POP_R ();                                  \
    int taken = (uint8 *)cur_class + offset - orig_ip;      \
    int fall_through = frame->ip - orig_ip;                 \
                                                            \
    gen_commit_for_branch (frame);                          \
    GEN_INSN (CMP, cc->cmp_reg, val, NEW_CONST (I4, 0));    \
    GEN_INSN (Op, cc->cmp_reg,                              \
              NEW_CONST (I4, taken),                        \
              NEW_CONST (I4, fall_through));                \
    goto cleanup_and_return;                                \
  } while (0)

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
#define DEF_OPCODE_IFA_W(Op) do {                           \
    JeffDOffset offset = read_uint32_align (frame->ip);     \
    JitReg val = POP_R ();                                  \
    int taken = (uint8 *)cur_class + offset - orig_ip;      \
    int fall_through = frame->ip - orig_ip;                 \
                                                            \
    gen_commit_for_branch (frame);                          \
    GEN_INSN (CMP, cc->cmp_reg, val, NEW_CONST (I4, 0));    \
    GEN_INSN (Op, cc->cmp_reg,                              \
              NEW_CONST (I4, taken),                        \
              NEW_CONST (I4, fall_through));                \
    goto cleanup_and_return;                                \
  } while (0)
#endif /* end of BEIHAI_ENABLE_JEFF_EXTENSION */

#define DEF_OPCODE_IF_ICMP(Op) do {                     \
    JeffOffset offset = read_uint16_align (frame->ip);  \
    JitReg val2 = POP_I ();                             \
    JitReg val1 = POP_I ();                             \
    int taken = (uint8 *)cur_class + offset - orig_ip;  \
    int fall_through = frame->ip - orig_ip;             \
                                                        \
    gen_commit_for_branch (frame);                      \
    GEN_INSN (CMP, cc->cmp_reg, val1, val2);            \
    GEN_INSN (Op, cc->cmp_reg,                          \
              NEW_CONST (I4, taken),                    \
              NEW_CONST (I4, fall_through));            \
    goto cleanup_and_return;                            \
  } while (0)

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
#define DEF_OPCODE_IF_ICMP_W(Op) do {                   \
    JeffDOffset offset = read_uint32_align (frame->ip); \
    JitReg val2 = POP_I ();                             \
    JitReg val1 = POP_I ();                             \
    int taken = (uint8 *)cur_class + offset - orig_ip;  \
    int fall_through = frame->ip - orig_ip;             \
                                                        \
    gen_commit_for_branch (frame);                      \
    GEN_INSN (CMP, cc->cmp_reg, val1, val2);            \
    GEN_INSN (Op, cc->cmp_reg,                          \
              NEW_CONST (I4, taken),                    \
              NEW_CONST (I4, fall_through));            \
    goto cleanup_and_return;                            \
  } while (0)
#endif /* end of BEIHAI_ENABLE_JEFF_EXTENSION */

#define DEF_OPCODE_IF_ACMP(Op) do {                     \
    JeffOffset offset = read_uint16_align (frame->ip);  \
    JitReg val2 = POP_R ();                             \
    JitReg val1 = POP_R ();                             \
    int taken = (uint8 *)cur_class + offset - orig_ip;  \
    int fall_through = frame->ip - orig_ip;             \
                                                        \
    gen_commit_for_branch (frame);                      \
    GEN_INSN (CMP, cc->cmp_reg, val1, val2);            \
    GEN_INSN (Op, cc->cmp_reg,                          \
              NEW_CONST (I4, taken),                    \
              NEW_CONST (I4, fall_through));            \
    goto cleanup_and_return;                            \
  } while (0)

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
#define DEF_OPCODE_IF_ACMP_W(Op) do {                   \
    JeffDOffset offset = read_uint32_align (frame->ip); \
    JitReg val2 = POP_R ();                             \
    JitReg val1 = POP_R ();                             \
    int taken = (uint8 *)cur_class + offset - orig_ip;  \
    int fall_through = frame->ip - orig_ip;             \
                                                        \
    gen_commit_for_branch (frame);                      \
    GEN_INSN (CMP, cc->cmp_reg, val1, val2);            \
    GEN_INSN (Op, cc->cmp_reg,                          \
              NEW_CONST (I4, taken),                    \
              NEW_CONST (I4, fall_through));            \
    goto cleanup_and_return;                            \
  } while (0)
#endif

#define DEF_OPCODE_XCMPL(Type) do {                 \
    JitReg val2 = POP_##Type ();                    \
    JitReg val1 = POP_##Type ();                    \
    JitReg result = jit_cc_new_reg_I4 (cc);         \
                                                    \
    if (jit_reg_kind (val1) == JIT_REG_KIND_F4      \
        || jit_reg_kind (val1) == JIT_REG_KIND_F8)  \
      GEN_INSN (XCMPLU, result, val1, val2);        \
    else                                            \
      GEN_INSN (XCMPLS, result, val1, val2);        \
    PUSH_I (result);                                \
  } while (0)

#define DEF_OPCODE_XCMPG(Type) do {                 \
    JitReg val2 = POP_##Type ();                    \
    JitReg val1 = POP_##Type ();                    \
    JitReg result = jit_cc_new_reg_I4 (cc);         \
                                                    \
    if (jit_reg_kind (val1) == JIT_REG_KIND_F4      \
        || jit_reg_kind (val1) == JIT_REG_KIND_F8)  \
      GEN_INSN (XCMPGU, result, val1, val2);        \
    else                                            \
      GEN_INSN (XCMPGS, result, val1, val2);        \
    PUSH_I (result);                                \
  } while (0)

#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
#define DEF_OPCODE_XLDC(ValPush, ValType) do {                      \
    JeffOffset offset = read_uint16_align (frame->ip);              \
    JitReg val = jit_cc_new_const_##ValType                         \
      (cc, *(CellType_##ValPush *)((uint8 *)cur_class + offset));   \
      PUSH_##ValPush (val);                                         \
  } while (0)
#else
#define DEF_OPCODE_XLDC(ValPush, ValType) do {                      \
    JeffDOffset offset = read_uint32_align (frame->ip);             \
    JitReg val = jit_cc_new_const_##ValType                         \
      (cc, *(CellType_##ValPush *)((uint8 *)cur_class + offset));   \
      PUSH_##ValPush (val);                                         \
  } while (0)
#endif /* end of BEIHAI_ENABLE_JEFF_EXTENSION */


/********************************************************************
 *                    Read/write operations
 ********************************************************************/

/* Read a value of given type from the address pointed to by the given
   pointer and increase the pointer to the position just after the
   value being read.  */

#define TEMPLATE_READ_VALUE(Type, p)                    \
  (p += sizeof (Type), *(Type *)(p - sizeof (Type)))

#define read_uint8(p)  TEMPLATE_READ_VALUE (uint8, p)
#define read_int8(p)   TEMPLATE_READ_VALUE (int8, p)
#define read_uint16(p) TEMPLATE_READ_VALUE (uint16, p)
#define read_int16(p)  TEMPLATE_READ_VALUE (int16, p)
#define read_uint32(p) TEMPLATE_READ_VALUE (uint32, p)
#define read_int32(p)  TEMPLATE_READ_VALUE (int32, p)

/* Read a value of given type from the aligned address pointed to by
   the given pointer and increase the pointer to the position just
   after the value being read.  */

#define TEMPLATE_READ_VALUE_ALIGN(Type, p)                              \
  (p = (uint8 *)align_uint ((unsigned)p, sizeof (Type)), read_##Type (p))

#define read_uint16_align(p) TEMPLATE_READ_VALUE_ALIGN (uint16, p)
#define read_int16_align(p)  TEMPLATE_READ_VALUE_ALIGN (int16, p)
#define read_uint32_align(p) TEMPLATE_READ_VALUE_ALIGN (uint32, p)
#define read_int32_align(p)  TEMPLATE_READ_VALUE_ALIGN (int32, p)

/* Read a various-length JEFF descriptor from the byte code.  */

static uint8*
read_jeff_descriptor_1 (JitReg *result_d, JitReg *result_c,
                        JitCompContext *cc, uint8 *p,
                        JeffClassHeaderLinked *c)
{
  union {uint32 i; JeffDescriptor d; } u;

  /* Initialize all bytes to 0 to avoid uninitialized values.  */
  u.i = 0;
  u.d.type = read_uint8 (p);
  u.d.dimension = 0;

  if ((u.d.type & JEFF_TYPE_MONO))
    u.d.dimension = 1;
  else if ((u.d.type & JEFF_TYPE_MULTI))
    u.d.dimension = read_uint8 (p);

  if (jeff_type_base (u.d.type) == JEFF_TYPE_OBJECT)
    {
      unsigned offset = read_uint16_align (p);
      *result_c = NEW_REL (CLASS, NONE, offset, jeff_get_class (c, offset, false));
    }
  else
    *result_c = NEW_CONST (I4, 0);

  *result_d = NEW_CONST (I4, u.i);

  return p;
}

#define read_jeff_descriptor(rd, rc, p, c) do {         \
    p = read_jeff_descriptor_1 (&rd, &rc, cc, p, c);    \
  } while (0)


/**
 * Generate an INVOKEMETHOD instruction but not insert it to the
 * current block.  It also generates code to commit frame status for
 * GC and exception, which may happen in the callee.
 *
 * @param frame the current frame
 * @param desc descriptor of the callee method
 * @param this_object this object register if it's not NULL
 *
 * @return the INVOKEMETHOD instruction
 */
static JitInsn*
gen_invoke_insn (Frame *frame, uint8 *desc, JitReg this_object)
{
  JitCompContext *cc = frame->cc;
  const int arg_num = *(uint16 *)desc;
  JitReg reg = 0;
  int first_opnd, i;
  JeffType return_type;
  JitInsn *insn;

  /* Just create the insn, don't insert it into the block.  */
  if (!(insn = jit_cc_new_insn (cc, INVOKEMETHOD, 0, 0,
                                arg_num + !!this_object)))
    return NULL;

  first_opnd = jit_insn_opndv_num (insn) - arg_num;

  for (desc += 2, i = 0; i < arg_num; i++)
    {
      JeffDescriptor *d = (JeffDescriptor *)desc;
      /* Use instruction's operand slot to store the type
         temporarily.  */
      *(jit_insn_opndv (insn, first_opnd + i)) = d->type;
      desc += jeff_descriptor_size (d);
    }

  return_type = ((JeffDescriptor *)desc)->type;

  for (i = arg_num - 1; i >= 0; i--)
    {
      JeffType type = *(jit_insn_opndv (insn, first_opnd + i));

      if ((type & JEFF_TYPE_REF))
        reg = pop_r (frame);
      else
        switch (jeff_type_base (type))
          {
          case JEFF_TYPE_SHORT:
          case JEFF_TYPE_INT:
          case JEFF_TYPE_BYTE:
          case JEFF_TYPE_CHAR:
          case JEFF_TYPE_BOOLEAN:
            reg = pop_i (frame);
            break;
          case JEFF_TYPE_LONG:
            reg = pop_l (frame);
            break;
          case JEFF_TYPE_FLOAT:
            reg = pop_f (frame);
            break;
          case JEFF_TYPE_DOUBLE:
            reg = pop_d (frame);
            break;
          default:
            jit_assert (0);
          }

      *(jit_insn_opndv (insn, first_opnd + i)) = reg;
    }

  if (this_object)
    /* It's a instance method, set the implicit this pointer and pop
       it out from the stack.  */
    {
      *(jit_insn_opndv (insn, 2)) = this_object;
      pop_r (frame);
    }

  /* Callee may cause GC or exception, so commit the status.  */
#if BEIHAI_ENABLE_JIT_LLVM == 0
  gen_commit_for_gc (frame);
#else
  gen_commit_for_all (frame);
#endif

  if (jeff_type_base (return_type) == JEFF_TYPE_VOID)
    reg = 0;
  else if ((return_type & JEFF_TYPE_REF))
    {
      reg = jit_cc_new_reg_I4 (frame->cc);
      push_r (frame, reg);
    }
  else
    switch (jeff_type_base (return_type))
      {
      case JEFF_TYPE_SHORT:
      case JEFF_TYPE_INT:
      case JEFF_TYPE_BYTE:
      case JEFF_TYPE_CHAR:
      case JEFF_TYPE_BOOLEAN:
        reg = jit_cc_new_reg_I4 (frame->cc);
        push_i (frame, reg);
        break;
      case JEFF_TYPE_LONG:
        reg = jit_cc_new_reg_I8 (frame->cc);
        push_l (frame, reg);
        break;
      case JEFF_TYPE_FLOAT:
        reg = jit_cc_new_reg_F4 (frame->cc);
        push_f (frame, reg);
        break;
      case JEFF_TYPE_DOUBLE:
        reg = jit_cc_new_reg_F8 (frame->cc);
        push_d (frame, reg);
        break;
      default:
        jit_assert (0);
      }

  *(jit_insn_opndv (insn, 0)) = reg;

  return insn;
}


static uint8*
translate (JitCompContext *cc, JitBlock *block, Frame *frame,
           JitBitmap *is_reached)
{
  JeffClassHeaderLinked *cur_class = frame->cur_class;
  uint8 opcode;
  uint8 *orig_ip, *frame_orig_ip = frame->ip;

  jit_bitmap_set_bit (is_reached, (uint32)frame->ip);

#if 0
  jit_printf("##V1.Translate line ");
  jeff_print_line_number (frame->cur_method,
                          (unsigned)frame->ip - (unsigned)frame->cur_class);
  jit_printf("\n");
  jit_printf(NULL);
#endif

  for (;;)
    {
      opcode = *frame->ip++;
      orig_ip = frame->ip;

#if BEIHAI_ENABLE_JIT_LLVM != 0
switch_again:
#endif
      switch (opcode)
        {
        case JEFF_OP_NOP:
          break;

        case JEFF_OP_ACONST_NULL:
          PUSH_R (NEW_CONST (I4, 0));
          break;

        case JEFF_OP_ICONST_M1:
          PUSH_I (NEW_CONST (I4, -1));
          break;

        case JEFF_OP_ICONST_0:
          PUSH_I (NEW_CONST (I4, 0));
          break;

        case JEFF_OP_ICONST_1:
          PUSH_I (NEW_CONST (I4, 1));
          break;

        case JEFF_OP_ICONST_2:
          PUSH_I (NEW_CONST (I4, 2));
          break;

        case JEFF_OP_ICONST_3:
          PUSH_I (NEW_CONST (I4, 3));
          break;

        case JEFF_OP_ICONST_4:
          PUSH_I (NEW_CONST (I4, 4));
          break;

        case JEFF_OP_ICONST_5:
          PUSH_I (NEW_CONST (I4, 5));
          break;

        case JEFF_OP_LCONST_0:
          PUSH_L (NEW_CONST (I8, 0));
          break;

        case JEFF_OP_LCONST_1:
          PUSH_L (NEW_CONST (I8, 1));
          break;

        case JEFF_OP_FCONST_0:
          PUSH_F (NEW_CONST (F4, 0));
          break;

        case JEFF_OP_FCONST_1:
          PUSH_F (NEW_CONST (F4, 1));
          break;

        case JEFF_OP_FCONST_2:
          PUSH_F (NEW_CONST (F4, 2));
          break;

        case JEFF_OP_DCONST_0:
          PUSH_D (NEW_CONST (F8, 0));
          break;

        case JEFF_OP_DCONST_1:
          PUSH_D (NEW_CONST (F8, 1));
          break;

        case JEFF_OP_BIPUSH:
          PUSH_I (NEW_CONST (I4, read_int8 (frame->ip)));
          break;

        case JEFF_OP_SIPUSH:
          PUSH_I (NEW_CONST (I4, read_int16_align (frame->ip)));
          break;

        case JEFF_OP_ILOAD:
          PUSH_I (LOCAL_I (read_uint8 (frame->ip)));
          break;

        case JEFF_OP_LLOAD:
          PUSH_L (LOCAL_L (read_uint8 (frame->ip)));
          break;

        case JEFF_OP_FLOAD:
          PUSH_F (LOCAL_F (read_uint8 (frame->ip)));
          break;

        case JEFF_OP_DLOAD:
          PUSH_D (LOCAL_D (read_uint8 (frame->ip)));
          break;

        case JEFF_OP_ALOAD:
          PUSH_R (LOCAL_R (read_uint8 (frame->ip)));
          break;

        case JEFF_OP_ILOAD_0:
          PUSH_I (LOCAL_I (0));
          break;

        case JEFF_OP_ILOAD_1:
          PUSH_I (LOCAL_I (1));
          break;

        case JEFF_OP_ILOAD_2:
          PUSH_I (LOCAL_I (2));
          break;

        case JEFF_OP_ILOAD_3:
          PUSH_I (LOCAL_I (3));
          break;

        case JEFF_OP_LLOAD_0:
          PUSH_L (LOCAL_L (0));
          break;

        case JEFF_OP_LLOAD_1:
          PUSH_L (LOCAL_L (1));
          break;

        case JEFF_OP_LLOAD_2:
          PUSH_L (LOCAL_L (2));
          break;

        case JEFF_OP_LLOAD_3:
          PUSH_L (LOCAL_L (3));
          break;

        case JEFF_OP_FLOAD_0:
          PUSH_F (LOCAL_F (0));
          break;

        case JEFF_OP_FLOAD_1:
          PUSH_F (LOCAL_F (1));
          break;

        case JEFF_OP_FLOAD_2:
          PUSH_F (LOCAL_F (2));
          break;

        case JEFF_OP_FLOAD_3:
          PUSH_F (LOCAL_F (3));
          break;

        case JEFF_OP_DLOAD_0:
          PUSH_D (LOCAL_D (0));
          break;

        case JEFF_OP_DLOAD_1:
          PUSH_D (LOCAL_D (1));
          break;

        case JEFF_OP_DLOAD_2:
          PUSH_D (LOCAL_D (2));
          break;

        case JEFF_OP_DLOAD_3:
          PUSH_D (LOCAL_D (3));
          break;

        case JEFF_OP_ALOAD_0:
          PUSH_R (LOCAL_R (0));
          break;

        case JEFF_OP_ALOAD_1:
          PUSH_R (LOCAL_R (1));
          break;

        case JEFF_OP_ALOAD_2:
          PUSH_R (LOCAL_R (2));
          break;

        case JEFF_OP_ALOAD_3:
          PUSH_R (LOCAL_R (3));
          break;

        case JEFF_OP_IALOAD:
          DEF_OPCODE_XALOAD (I4, I4, I);
          break;

        case JEFF_OP_LALOAD:
          DEF_OPCODE_XALOAD (I8, I8, L);
          break;

        case JEFF_OP_FALOAD:
          DEF_OPCODE_XALOAD (F4, F4, F);
          break;

        case JEFF_OP_DALOAD:
          DEF_OPCODE_XALOAD (F8, F8, D);
          break;

        case JEFF_OP_AALOAD:
          DEF_OPCODE_XALOAD (I4, I4, R);
          break;

        case JEFF_OP_BALOAD:
          DEF_OPCODE_XALOAD (I1, I4, I);
          break;

        case JEFF_OP_CALOAD:
          DEF_OPCODE_XALOAD (U2, I4, I);
          break;

        case JEFF_OP_SALOAD:
          DEF_OPCODE_XALOAD (I2, I4, I);
          break;

        case JEFF_OP_ISTORE:
          SET_LOCAL_I (read_uint8 (frame->ip), POP_I ());
          break;

        case JEFF_OP_LSTORE:
          SET_LOCAL_L (read_uint8 (frame->ip), POP_L ());
          break;

        case JEFF_OP_FSTORE:
          SET_LOCAL_F (read_uint8 (frame->ip), POP_F ());
          break;

        case JEFF_OP_DSTORE:
          SET_LOCAL_D (read_uint8 (frame->ip), POP_D ());
          break;

        case JEFF_OP_ASTORE:
          STORE_LOCAL_R (read_uint8 (frame->ip));
          break;

        case JEFF_OP_ISTORE_0:
          SET_LOCAL_I (0, POP_I ());
          break;

        case JEFF_OP_ISTORE_1:
          SET_LOCAL_I (1, POP_I ());
          break;

        case JEFF_OP_ISTORE_2:
          SET_LOCAL_I (2, POP_I ());
          break;

        case JEFF_OP_ISTORE_3:
          SET_LOCAL_I (3, POP_I ());
          break;

        case JEFF_OP_LSTORE_0:
          SET_LOCAL_L (0, POP_L ());
          break;

        case JEFF_OP_LSTORE_1:
          SET_LOCAL_L (1, POP_L ());
          break;

        case JEFF_OP_LSTORE_2:
          SET_LOCAL_L (2, POP_L ());
          break;

        case JEFF_OP_LSTORE_3:
          SET_LOCAL_L (3, POP_L ());
          break;

        case JEFF_OP_FSTORE_0:
          SET_LOCAL_F (0, POP_F ());
          break;

        case JEFF_OP_FSTORE_1:
          SET_LOCAL_F (1, POP_F ());
          break;

        case JEFF_OP_FSTORE_2:
          SET_LOCAL_F (2, POP_F ());
          break;

        case JEFF_OP_FSTORE_3:
          SET_LOCAL_F (3, POP_F ());
          break;

        case JEFF_OP_DSTORE_0:
          SET_LOCAL_D (0, POP_D ());
          break;

        case JEFF_OP_DSTORE_1:
          SET_LOCAL_D (1, POP_D ());
          break;

        case JEFF_OP_DSTORE_2:
          SET_LOCAL_D (2, POP_D ());
          break;

        case JEFF_OP_DSTORE_3:
          SET_LOCAL_D (3, POP_D ());
          break;

        case JEFF_OP_ASTORE_0:
          STORE_LOCAL_R (0);
          break;

        case JEFF_OP_ASTORE_1:
          STORE_LOCAL_R (1);
          break;

        case JEFF_OP_ASTORE_2:
          STORE_LOCAL_R (2);
          break;

        case JEFF_OP_ASTORE_3:
          STORE_LOCAL_R (3);
          break;

        case JEFF_OP_IASTORE:
          DEF_OPCODE_XASTORE (I4, I);
          break;

        case JEFF_OP_LASTORE:
          DEF_OPCODE_XASTORE (I8, L);
          break;

        case JEFF_OP_FASTORE:
          DEF_OPCODE_XASTORE (F4, F);
          break;

        case JEFF_OP_DASTORE:
          DEF_OPCODE_XASTORE (F8, D);
          break;

        case JEFF_OP_AASTORE:
          {
            JitReg value = POP_R ();
            JitReg index = POP_I ();
            JitReg array = POP_R ();
            JitReg offset;
            JitReg base = gen_array_addr (frame, array, index,
                                          CUR_IP_OFFSET (),
                                          SIZE_I4, &offset);
            GEN_INSN_CHK (CHKARRVAL, CUR_IP_OFFSET (), array, value, FRAME_IP ());
            GEN_INSN (STI4, value, base, offset);
            break;
          }

        case JEFF_OP_BASTORE:
          DEF_OPCODE_XASTORE (I1, I);
          break;

        case JEFF_OP_CASTORE:
          DEF_OPCODE_XASTORE (I2, I);
          break;

        case JEFF_OP_SASTORE:
          DEF_OPCODE_XASTORE (I2, I);
          break;

        case JEFF_OP_POP:
          POP (1);
          break;

        case JEFF_OP_POP2:
          POP (2);
          break;

        case JEFF_OP_DUP:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[0] = frame->sp[-1];
            frame->sp++;
            break;
          }

        case JEFF_OP_DUP_X1:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[0] = frame->sp[-1];
            frame->sp[-1] = frame->sp[-2];
            frame->sp[-2] = frame->sp[0];
            frame->sp++;
            break;
          }

        case JEFF_OP_DUP_X2:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0
                || jit_reg_kind (frame->sp[-3].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[0] = frame->sp[-1];
            frame->sp[-1] = frame->sp[-2];
            frame->sp[-2] = frame->sp[-3];
            frame->sp[-3] = frame->sp[0];
            frame->sp++;
            break;
          }

        case JEFF_OP_DUP2:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[1] = frame->sp[-1];
            frame->sp[0] = frame->sp[-2];
            frame->sp += 2;
            break;
          }

        case JEFF_OP_DUP2_X1:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0
                || jit_reg_kind (frame->sp[-3].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[1] = frame->sp[-1];
            frame->sp[0] = frame->sp[-2];
            frame->sp[-1] = frame->sp[-3];
            frame->sp[-2] = frame->sp[1];
            frame->sp[-3] = frame->sp[0];
            frame->sp += 2;
            break;
          }

        case JEFF_OP_DUP2_X2:
          {
            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0
                || jit_reg_kind (frame->sp[-3].reg) == 0
                || jit_reg_kind (frame->sp[-4].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            frame->sp[1] = frame->sp[-1];
            frame->sp[0] = frame->sp[-2];
            frame->sp[-1] = frame->sp[-3];
            frame->sp[-2] = frame->sp[-4];
            frame->sp[-3] = frame->sp[1];
            frame->sp[-4] = frame->sp[0];
            frame->sp += 2;
            break;
          }

        case JEFF_OP_SWAP:
          {
            ValueSlot tmp;

            if (jit_reg_kind (frame->sp[-1].reg) == 0
                || jit_reg_kind (frame->sp[-2].reg) == 0)
              {
                /* Unknown reg info, give up compilation. */
                /*
                orig_ip = NULL;
                goto cleanup_and_return;
                */
                goto gen_leave_and_return;
              }

            tmp = frame->sp[-1];
            frame->sp[-1] = frame->sp[-2];
            frame->sp[-2] = tmp;
            break;
          }

        case JEFF_OP_IADD:
          DEF_OPCODE_MATH_BINARY (I, I, I, ADD);
          break;

        case JEFF_OP_LADD:
          DEF_OPCODE_MATH_BINARY (L, L, L, ADD);
          break;

        case JEFF_OP_FADD:
          DEF_OPCODE_MATH_BINARY (F, F, F, ADD);
          break;

        case JEFF_OP_DADD:
          DEF_OPCODE_MATH_BINARY (D, D, D, ADD);
          break;

        case JEFF_OP_ISUB:
          DEF_OPCODE_MATH_BINARY (I, I, I, SUB);
          break;

        case JEFF_OP_LSUB:
          DEF_OPCODE_MATH_BINARY (L, L, L, SUB);
          break;

        case JEFF_OP_FSUB:
          DEF_OPCODE_MATH_BINARY (F, F, F, SUB);
          break;

        case JEFF_OP_DSUB:
          DEF_OPCODE_MATH_BINARY (D, D, D, SUB);
          break;

        case JEFF_OP_IMUL:
          DEF_OPCODE_MATH_BINARY (I, I, I, MUL);
          break;

        case JEFF_OP_LMUL:
          DEF_OPCODE_MATH_BINARY (L, L, L, MUL);
          break;

        case JEFF_OP_FMUL:
          DEF_OPCODE_MATH_BINARY (F, F, F, MUL);
          break;

        case JEFF_OP_DMUL:
          DEF_OPCODE_MATH_BINARY (D, D, D, MUL);
          break;

        case JEFF_OP_IDIV:
          DEF_OPCODE_MATH_DIV_REM (I, I4, DIV);
          break;

        case JEFF_OP_LDIV:
          DEF_OPCODE_MATH_DIV_REM (L, I8, DIV);
          break;

        case JEFF_OP_FDIV:
          DEF_OPCODE_MATH_BINARY (F, F, F, DIV);
          break;

        case JEFF_OP_DDIV:
          DEF_OPCODE_MATH_BINARY (D, D, D, DIV);
          break;

        case JEFF_OP_IREM:
          DEF_OPCODE_MATH_DIV_REM (I, I4, REM);
          break;

        case JEFF_OP_LREM:
          DEF_OPCODE_MATH_DIV_REM (L, I8, REM);
          break;

        case JEFF_OP_FREM:
          DEF_OPCODE_MATH_BINARY (F, F, F, REM);
          break;

        case JEFF_OP_DREM:
          DEF_OPCODE_MATH_BINARY (D, D, D, REM);
          break;

        case JEFF_OP_INEG:
          DEF_OPCODE_MATH_UNARY (I, I, NEG);
          break;

        case JEFF_OP_LNEG:
          DEF_OPCODE_MATH_UNARY (L, L, NEG);
          break;

        case JEFF_OP_FNEG:
          DEF_OPCODE_MATH_UNARY (F, F, NEG);
          break;

        case JEFF_OP_DNEG:
          DEF_OPCODE_MATH_UNARY (D, D, NEG);
          break;

        case JEFF_OP_ISHL:
          DEF_OPCODE_MATH_BINARY (I, I, I, SHL);
          break;

        case JEFF_OP_LSHL:
          DEF_OPCODE_MATH_BINARY (L, I, L, SHL);
          break;

        case JEFF_OP_ISHR:
          DEF_OPCODE_MATH_BINARY (I, I, I, SHRS);
          break;

        case JEFF_OP_LSHR:
          DEF_OPCODE_MATH_BINARY (L, I, L, SHRS);
          break;

        case JEFF_OP_IUSHR:
          DEF_OPCODE_MATH_BINARY (I, I, I, SHRU);
          break;

        case JEFF_OP_LUSHR:
          DEF_OPCODE_MATH_BINARY (L, I, L, SHRU);
          break;

        case JEFF_OP_IAND:
          DEF_OPCODE_MATH_BINARY (I, I, I, AND);
          break;

        case JEFF_OP_LAND:
          DEF_OPCODE_MATH_BINARY (L, L, L, AND);
          break;

        case JEFF_OP_IOR:
          DEF_OPCODE_MATH_BINARY (I, I, I, OR);
          break;

        case JEFF_OP_LOR:
          DEF_OPCODE_MATH_BINARY (L, L, L, OR);
          break;

        case JEFF_OP_IXOR:
          DEF_OPCODE_MATH_BINARY (I, I, I, XOR);
          break;

        case JEFF_OP_LXOR:
          DEF_OPCODE_MATH_BINARY (L, L, L, XOR);
          break;

        case JEFF_OP_IINC:
          {
            unsigned var_index;
            int inc_val;
            JitReg result;

            var_index = read_uint8 (frame->ip);
            inc_val = read_int8 (frame->ip);
            GEN_INSN_NORM (I4, result, ADD, 0, LOCAL_I (var_index),
                           NEW_CONST (I4, inc_val));
            SET_LOCAL_I (var_index, result);
            break;
          }

        case JEFF_OP_I2L:
          DEF_OPCODE_MATH_UNARY (I, L, I4TOI8);
          break;

        case JEFF_OP_I2F:
          DEF_OPCODE_MATH_UNARY (I, F, I4TOF4);
          break;

        case JEFF_OP_I2D:
          DEF_OPCODE_MATH_UNARY (I, D, I4TOF8);
          break;

        case JEFF_OP_L2I:
          DEF_OPCODE_MATH_UNARY (L, I, I8TOI4);
          break;

        case JEFF_OP_L2F:
          DEF_OPCODE_MATH_UNARY (L, F, I8TOF4);
          break;

        case JEFF_OP_L2D:
          DEF_OPCODE_MATH_UNARY (L, D, I8TOF8);
          break;

        case JEFF_OP_F2I:
          DEF_OPCODE_MATH_UNARY (F, I, F4TOI4);
          break;

        case JEFF_OP_F2L:
          DEF_OPCODE_MATH_UNARY (F, L, F4TOI8);
          break;

        case JEFF_OP_F2D:
          DEF_OPCODE_MATH_UNARY (F, D, F4TOF8);
          break;

        case JEFF_OP_D2I:
          DEF_OPCODE_MATH_UNARY (D, I, F8TOI4);
          break;

        case JEFF_OP_D2L:
          DEF_OPCODE_MATH_UNARY (D, L, F8TOI8);
          break;

        case JEFF_OP_D2F:
          DEF_OPCODE_MATH_UNARY (D, F, F8TOF4);
          break;

        case JEFF_OP_I2B:
          DEF_OPCODE_MATH_UNARY (I, I, I4TOI1);
          break;

        case JEFF_OP_I2C:
          DEF_OPCODE_MATH_UNARY (I, I, I4TOU2);
          break;

        case JEFF_OP_I2S:
          DEF_OPCODE_MATH_UNARY (I, I, I4TOI2);
          break;

        case JEFF_OP_LCMP:
          DEF_OPCODE_XCMPL (L);
          break;

        case JEFF_OP_FCMPL:
          DEF_OPCODE_XCMPL (F);
          break;

        case JEFF_OP_FCMPG:
          DEF_OPCODE_XCMPG (F);
          break;

        case JEFF_OP_DCMPL:
          DEF_OPCODE_XCMPL (D);
          break;

        case JEFF_OP_DCMPG:
          DEF_OPCODE_XCMPG (D);
          break;

        case JEFF_OP_IFEQ:
          DEF_OPCODE_IF (BEQ);
          break;

        case JEFF_OP_IFNE:
          DEF_OPCODE_IF (BNE);
          break;

        case JEFF_OP_IFLT:
          DEF_OPCODE_IF (BLTS);
          break;

        case JEFF_OP_IFGE:
          DEF_OPCODE_IF (BGES);
          break;

        case JEFF_OP_IFGT:
          DEF_OPCODE_IF (BGTS);
          break;

        case JEFF_OP_IFLE:
          DEF_OPCODE_IF (BLES);
          break;

        case JEFF_OP_IF_ICMPEQ:
          DEF_OPCODE_IF_ICMP (BEQ);
          break;

        case JEFF_OP_IF_ICMPNE:
          DEF_OPCODE_IF_ICMP (BNE);
          break;

        case JEFF_OP_IF_ICMPLT:
          DEF_OPCODE_IF_ICMP (BLTS);
          break;

        case JEFF_OP_IF_ICMPGE:
          DEF_OPCODE_IF_ICMP (BGES);
          break;

        case JEFF_OP_IF_ICMPGT:
          DEF_OPCODE_IF_ICMP (BGTS);
          break;

        case JEFF_OP_IF_ICMPLE:
          DEF_OPCODE_IF_ICMP (BLES);
          break;

        case JEFF_OP_IF_ACMPEQ:
          DEF_OPCODE_IF_ACMP (BEQ);
          break;

        case JEFF_OP_IF_ACMPNE:
          DEF_OPCODE_IF_ACMP (BNE);
          break;

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_IFEQ_W:
          DEF_OPCODE_IF_W (BEQ);
          break;

        case JEFF_OP_IFNE_W:
          DEF_OPCODE_IF_W (BNE);
          break;

        case JEFF_OP_IFLT_W:
          DEF_OPCODE_IF_W (BLTS);
          break;

        case JEFF_OP_IFGE_W:
          DEF_OPCODE_IF_W (BGES);
          break;

        case JEFF_OP_IFGT_W:
          DEF_OPCODE_IF_W (BGTS);
          break;

        case JEFF_OP_IFLE_W:
          DEF_OPCODE_IF_W (BLES);
          break;

        case JEFF_OP_IF_ICMPEQ_W:
          DEF_OPCODE_IF_ICMP_W (BEQ);
          break;

        case JEFF_OP_IF_ICMPNE_W:
          DEF_OPCODE_IF_ICMP_W (BNE);
          break;

        case JEFF_OP_IF_ICMPLT_W:
          DEF_OPCODE_IF_ICMP_W (BLTS);
          break;

        case JEFF_OP_IF_ICMPGE_W:
          DEF_OPCODE_IF_ICMP_W (BGES);
          break;

        case JEFF_OP_IF_ICMPGT_W:
          DEF_OPCODE_IF_ICMP_W (BGTS);
          break;

        case JEFF_OP_IF_ICMPLE_W:
          DEF_OPCODE_IF_ICMP_W (BLES);
          break;

        case JEFF_OP_IF_ACMPEQ_W:
          DEF_OPCODE_IF_ACMP_W (BEQ);
          break;

        case JEFF_OP_IF_ACMPNE_W:
          DEF_OPCODE_IF_ACMP_W (BNE);
          break;
#endif

        case JEFF_OP_GOTO:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_GOTO_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            JeffOffset offset = read_uint16_align (frame->ip);
#else
            JeffDOffset offset = (opcode == JEFF_OP_GOTO)
                                 ? read_uint16_align (frame->ip)
                                 : read_uint32_align (frame->ip);
#endif
            uint8 *new_ip = (uint8 *)cur_class + offset;

            if (jit_globals.options.frontend_enable_goto_coalescing
                /* Only coalesce blocks that are in the region range
                   and that have not been reached to avoid infinite
                   goto loops.  */
                && jit_bitmap_is_in_range (is_reached, (uint32)new_ip)
                && !jit_bitmap_get_bit (is_reached, (uint32)new_ip))
              {
                jit_bitmap_set_bit (is_reached, (uint32)new_ip);
                frame->ip = new_ip;
                break;
              }
            else
              {
                int taken_offset = new_ip - orig_ip;
                gen_commit_for_branch (frame);
                GEN_INSN (JMP, NEW_CONST (I4, taken_offset));
                goto cleanup_and_return;
              }
          }

#if BEIHAI_ENABLE_OPCODE_SUBRT != 0
        case JEFF_OP_JSR:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_JSR_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            JeffOffset offset = read_uint16_align (frame->ip);
#else
            JeffDOffset offset = (opcode == JEFF_OP_JSR)
                                  ? read_uint16_align (frame->ip)
                                  : read_uint32_align (frame->ip);
#endif
            uint8 *new_ip = (uint8 *)cur_class + offset;
            int taken_offset = new_ip - orig_ip;
            JitReg val = NEW_CONST (I4, (int32)(frame->ip - (uint8*)cur_class));

            PUSH_I (val);
            gen_commit_for_branch (frame);
            GEN_INSN (JMP, NEW_CONST (I4, taken_offset));
            goto cleanup_and_return;
          }

        case JEFF_OP_RET_W:
          {
            /* TODO: translate OP_RET_W
            unsigned var_index = read_uint16_align (frame->ip);
            JitReg val = LOCAL_I (var_index);

            gen_commit_for_branch (frame);
            GEN_INSN (JMP, val);
            goto cleanup_and_return;
            */
            jit_printf("V5.JIT: unsupported opcode JEFF_OP_RET_W!\n");
            /*
            orig_ip = NULL;
            goto cleanup_and_return;
            */
            goto gen_leave_and_return;
          }
#endif

        case JEFF_OP_TABLESWITCH:
          {
            JeffOffset offset = read_uint16_align (frame->ip);
            int32 low_value = read_int32_align (frame->ip);
            int32 high_value = read_int32 (frame->ip), i;
            JeffOffset *jump_table = (JeffOffset *)frame->ip;
            JitReg value = POP_I ();
            JitInsn *insn;
            JitOpndTableSwitch *opnd;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (TABLESWITCH, value, low_value, high_value)))
              break;

            opnd = jit_insn_opndts (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i <= high_value - low_value; i++)
              opnd->targets[i] = NEW_CONST
                (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);

            goto cleanup_and_return;
          }

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_TABLESWITCH_W:
          {
            JeffDOffset offset = read_uint32_align (frame->ip);
            int32 low_value = read_int32_align (frame->ip);
            int32 high_value = read_int32 (frame->ip), i;
            JeffDOffset *jump_table = (JeffDOffset *)frame->ip;
            JitReg value = POP_I ();
            JitInsn *insn;
            JitOpndTableSwitch *opnd;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (TABLESWITCH, value, low_value, high_value)))
              break;

            opnd = jit_insn_opndts (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i <= high_value - low_value; i++)
              opnd->targets[i] = NEW_CONST
                (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);

            goto cleanup_and_return;
          }
#endif

        case JEFF_OP_LOOKUPSWITCH:
          {
            JeffOffset offset = read_uint16_align (frame->ip);
            unsigned pairs_num = read_uint16 (frame->ip), i;
            int32 *match_table = (int32 *)align_uint ((unsigned)frame->ip, 4);
            JeffOffset *jump_table = (JeffOffset *)(match_table + pairs_num);
            JitReg value = POP_I ();
            JitInsn *insn;
            JitOpndLookupSwitch *opnd;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (LOOKUPSWITCH, value, pairs_num)))
              break;

            opnd = jit_insn_opndls (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i < pairs_num; i++)
              {
                opnd->match_pairs[i].value = match_table[i];
                opnd->match_pairs[i].target = NEW_CONST
                  (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);
              }

            goto cleanup_and_return;
          }

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_LOOKUPSWITCH_W:
          {
            JeffDOffset offset = read_uint32_align (frame->ip);
            unsigned pairs_num = read_uint16 (frame->ip), i;
            int32 *match_table = (int32 *)align_uint ((unsigned)frame->ip, 4);
            JeffDOffset *jump_table = (JeffDOffset *)(match_table + pairs_num);
            JitReg value = POP_I ();
            JitInsn *insn;
            JitOpndLookupSwitch *opnd;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (LOOKUPSWITCH, value, pairs_num)))
              break;

            opnd = jit_insn_opndls (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i < pairs_num; i++)
              {
                opnd->match_pairs[i].value = match_table[i];
                opnd->match_pairs[i].target = NEW_CONST
                  (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);
              }

            goto cleanup_and_return;
          }
#endif

        case JEFF_OP_IRETURN:
        case JEFF_OP_LRETURN:
        case JEFF_OP_FRETURN:
        case JEFF_OP_DRETURN:
        case JEFF_OP_ARETURN:
        case JEFF_OP_RETURN:
          if (frame->cur_method->access_flag & JEFF_ACC_SYNCHRONIZED)
            {
              JitInsn *insn;
              JitReg obj = jit_cc_new_reg_I4 (cc);

              gen_commit_for_gc (frame);
              if (frame->cur_method->access_flag & JEFF_ACC_STATIC)
                {
                  if (!(insn = GEN_INSN (INVOKENATIVE, obj,
                          NEW_INTRINSIC (jeff_runtime_get_class_object), 1)))
                    break;

                  *(jit_insn_opndv (insn, 2)) = NEW_REL (CLASS, NONE, 0, frame->cur_class);
                }
              else
                GEN_INSN (LDI4, obj, cc->fp_reg, NEW_CONST (I4, offset_of_local (0)));

              if (!(insn = GEN_INSN (INVOKENATIVE, 0,
                      NEW_INTRINSIC (jeff_sync_object_unlock), 2)))
                break;

              *(jit_insn_opndv (insn, 2)) = cc->self_reg;
              *(jit_insn_opndv (insn, 3)) = obj;
            }

          switch (opcode)
            {
              case JEFF_OP_IRETURN:
                GEN_INSN (RETURN, POP_I ());
                break;
              case JEFF_OP_LRETURN:
                GEN_INSN (RETURN, POP_L ());
                break;
              case JEFF_OP_FRETURN:
                GEN_INSN (RETURN, POP_F ());
                break;
              case JEFF_OP_DRETURN:
                GEN_INSN (RETURN, POP_D ());
                break;
              case JEFF_OP_ARETURN:
                GEN_INSN (ARETURN, POP_R ());
                break;
              case JEFF_OP_RETURN:
                GEN_INSN (RETURN, 0);
                break;
          }
          goto cleanup_and_return;

        case JEFF_OP_GETSTATIC:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_GETSTATIC_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_GETSTATIC)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffFieldLinked *field = jeff_get_resolved_field (cur_class, offset, false);
            JeffClassHeaderLinked *field_class = jeff_get_field_class (field);
            JitReg cil;
            JitInsn *insn;

            if ((insn = GEN_INSN_NORM (I4, cil, CLASSBASE, 0,
                                       NEW_REL (FIELD, CLASS, offset, field_class)))
                && field_class != cur_class)
              /* Commit for GC and exception only when the field class
                 is not same as the current class.  */
              {
                /* Temporarily unlink the insn.  */
                jit_insn_unlink (insn);
                gen_commit_for_gc (frame);
                /* Insert it back.  */
                jit_block_append_insn (frame->block, insn);
              }

            GET_FIELD (frame, cil, field->field_type,
                       (offsetof (JeffClassInstanceLocal, static_area)
                        + jeff_get_field_data_offset (field)),
                       jeff_class_same_file (field_class, cur_class) ? 0 : offset);
            break;
          }

        case JEFF_OP_PUTSTATIC:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_PUTSTATIC_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_PUTSTATIC)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffFieldLinked *field = jeff_get_resolved_field (cur_class, offset, false);
            JeffClassHeaderLinked *field_class = jeff_get_field_class (field);
            JitReg cil;
            JitInsn *insn;

            if ((insn = GEN_INSN_NORM (I4, cil, CLASSBASE, 0,
                                       NEW_REL (FIELD, CLASS, offset, field_class)))
                && field_class != cur_class)
              /* Commit for GC and exception only when the field class
                 is not same as the current class.  */
              {
                /* Temporarily unlink the insn.  */
                jit_insn_unlink (insn);
                gen_commit_for_gc (frame);
                /* Insert it back.  */
                jit_block_append_insn (frame->block, insn);
              }

            PUT_FIELD (frame, cil, field->field_type,
                       (offsetof (JeffClassInstanceLocal, static_area)
                        + jeff_get_field_data_offset (field)),
                       jeff_class_same_file (field_class, cur_class) ? 0 : offset);
            break;
          }

        case JEFF_OP_GETFIELD:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_GETFIELD_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_GETFIELD)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffFieldLinked *field = jeff_get_resolved_field (cur_class, offset, false);
            JeffClassHeaderLinked *field_class = jeff_get_field_class (field);
            JitReg object = POP_R ();
            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), object, FRAME_IP ());
            GET_FIELD (frame, object, field->field_type,
                       jeff_get_field_data_offset (field),
                       jeff_class_same_file (field_class, cur_class) ? 0 : offset);
            break;
          }

        case JEFF_OP_PUTFIELD:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_PUTFIELD_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_PUTFIELD)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffFieldLinked *field = jeff_get_resolved_field (cur_class, offset, false);
            JeffClassHeaderLinked *field_class = jeff_get_field_class (field);
            unsigned value_size = jeff_type_size (field->field_type);
            unsigned slot = align_uint (value_size, 4) / 4 + 1;
            JitReg object = STACK_R (slot);
            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), object, FRAME_IP ());
            PUT_FIELD (frame, object, field->field_type,
                       jeff_get_field_data_offset (field),
                       jeff_class_same_file (field_class, cur_class) ? 0 : offset);
            POP (1);
            break;
          }

        case JEFF_OP_INVOKEVIRTUAL:
        case JEFF_OP_INVOKEINTERFACE:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_INVOKEVIRTUAL_W:
        case JEFF_OP_INVOKEINTERFACE_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_INVOKEVIRTUAL
                               || opcode == JEFF_OP_INVOKEINTERFACE)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffMethodLinked *method = jeff_get_resolved_method (cur_class, offset, false);
            JeffClassHeaderLinked *method_class = jeff_get_method_class (method);
            JitReg object = STACK_R (method->stack_cell_num);
            JitReg vtable_reg, method_reg;
            uint8 *desc = (uint8 *)jeff_get_method_descriptor (method);
            JitInsn *insn, *insn1;

            if (!(insn = gen_invoke_insn (frame, desc, object)))
              break;

            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), object, FRAME_IP ());

            if (opcode == JEFF_OP_INVOKEINTERFACE
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
                || opcode == JEFF_OP_INVOKEINTERFACE_W
#endif
                || (method_class->access_flag & JEFF_ACC_INTERFACE))
              {
                method_reg = jit_cc_new_reg_I4 (cc);

                /* The status has been committed by gen_invoke_insn,
                   so don't need to call gen_commit_for_exception.  */
                if (!(insn1 = GEN_INSN
                      (INVOKENATIVE, method_reg,
                       NEW_INTRINSIC (jeff_interp_select_method_interface), 2)))
                  break;

                *(jit_insn_opndv (insn1, 2)) = object;
                *(jit_insn_opndv (insn1, 3)) = NEW_REL (METHOD, NONE, offset, method);
              }
            else
              {
                unsigned index = jeff_get_method_vtable_index (method);
                GEN_INSN_NORM (I4, vtable_reg, LDVTABLE, 0, object);
                GEN_INSN_NORM (I4, method_reg, LDMETHOD, 0, vtable_reg,
                               NEW_REL (METHOD, MTDIDX, offset, index));
              }

            *(jit_insn_opndv (insn, 1)) = method_reg;
            jit_block_append_insn (block, insn);
            break;
          }

        case JEFF_OP_INVOKESPECIAL:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_INVOKESPECIAL_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_INVOKESPECIAL)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffMethodLinked *method = jeff_get_resolved_method (cur_class, offset, false);
            JeffClassHeaderLinked *method_class = jeff_get_method_class (method);
            JeffClassHeaderLinked *super_class;
            JitReg object = STACK_R (method->stack_cell_num);
            uint8 *desc = (uint8 *)jeff_get_method_descriptor (method);
            JitInsn *insn;

            if (!(insn = gen_invoke_insn (frame, desc, object)))
              break;

            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), object, FRAME_IP ());

            if ((cur_class->access_flag & JEFF_ACC_SUPER)
                && method_class != cur_class
                && !(method->access_flag & JEFF_ACC_INIT))
              {
                super_class = jeff_get_super_class (cur_class);
                if (super_class != method_class
                    && jeff_is_super_class (method_class, super_class))
                  method = jeff_select_method_virtual (super_class, method);
              }

            *(jit_insn_opndv (insn, 1)) = NEW_REL (METHOD, SPEMTD, offset, method);
            jit_block_append_insn (block, insn);
            break;
          }

        case JEFF_OP_INVOKESTATIC:
#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_INVOKESTATIC_W:
#endif
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned offset = read_uint16_align (frame->ip);
#else
            unsigned offset = (opcode == JEFF_OP_INVOKESTATIC)
                               ? read_uint16_align (frame->ip)
                               : read_uint32_align (frame->ip);
#endif
            JeffMethodLinked *method = jeff_get_resolved_method (cur_class, offset, false);
            uint8 *desc = (uint8 *)jeff_get_method_descriptor (method);
            JeffClassHeaderLinked *method_class = jeff_get_method_class (method);
            JitInsn *insn;
            JitReg cil;

            /* Run CLASSBASE to initialize the class if the target
               method's class is different from the current one.  This
               must be generated before calling gen_invoke_insn
               because parameters popped off by gen_invoke_insn
               contain references.  */
            if (method_class != cur_class)
              {
                gen_commit_for_gc (frame);
                GEN_INSN_NORM (I4, cil, CLASSBASE, 0,
                               NEW_REL (METHOD, CLASS, offset, method_class));
              }

            if (!(insn = gen_invoke_insn (frame, desc, 0)))
              break;

            *(jit_insn_opndv (insn, 1)) = NEW_REL (METHOD, NONE, offset, method);
            jit_block_append_insn (block, insn);
            break;
          }

        case JEFF_OP_NEW:
          {
            JeffOffset offset = read_uint16_align (frame->ip);
            JeffClassHeaderLinked *object_class = jeff_get_class
              (cur_class, offset, false);
            JitReg object = jit_cc_new_reg_I4 (cc);
            JitInsn *insn;

            gen_commit_for_gc (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, object,
                                   NEW_INTRINSIC (jeff_interp_new_object), 2)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = NEW_REL (CLASS, NONE, offset, object_class);
            PUSH_R (object);
            break;
          }

        case JEFF_OP_NEWARRAY:
          {
            JitReg array = jit_cc_new_reg_I4 (cc);
            JitReg d, c;
            JitReg length = POP_I ();
            JitInsn *insn;

            read_jeff_descriptor (d, c, frame->ip, cur_class);
            gen_commit_for_gc (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, array,
                                   NEW_INTRINSIC (jeff_interp_new_array), 4)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = d;
            *(jit_insn_opndv (insn, 4)) = c;
            *(jit_insn_opndv (insn, 5)) = length;
            PUSH_R (array);
            break;
          }

        case JEFF_OP_ARRAYLENGTH:
          {
            JitReg array = POP_R ();
            JitReg result;
            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), array, FRAME_IP ());
            GEN_INSN_NORM (I4, result, ARRAYLEN, 0, array);
            PUSH_I (result);
            break;
          }

        case JEFF_OP_ATHROW:
          {
            JitInsn *insn;
            JitReg exc = STACK_R (1);

            gen_commit_for_exception (frame);
            gen_commit_sp_ip (frame);

            if (!(insn = GEN_INSN (CALLNATIVE, 0,
                                   NEW_INTRINSIC (jeff_interp_athrow), 1))) {
              break;
            }

            *(jit_insn_opndv (insn, 2)) = exc;
            GEN_INSN (LEAVE, NEW_CONST (I4, JIT_INTERP_ACTION_THROWN),
                      CUR_IP_OFFSET (), 0);
            goto cleanup_and_return;
          }

        case JEFF_OP_CHECKCAST:
          {
            JitReg d, c;
            JitReg obj = STACK_R (1);
            read_jeff_descriptor (d, c, frame->ip, cur_class);
            GEN_INSN_CHK (CHKCAST, CUR_IP_OFFSET (), obj, d, c, FRAME_IP ());
            break;
          }

        case JEFF_OP_INSTANCEOF:
          {
            JitReg d, c;
            JitReg obj = POP_R ();
            JitReg result = jit_cc_new_reg_I4 (cc);
            JitInsn *insn;

            read_jeff_descriptor (d, c, frame->ip, cur_class);

            if (!(insn = GEN_INSN (CALLNATIVE, result,
                                   NEW_INTRINSIC (jeff_interp_instanceof), 3))) {
              break;
            }

            *(jit_insn_opndv (insn, 2)) = obj;
            *(jit_insn_opndv (insn, 3)) = d;
            *(jit_insn_opndv (insn, 4)) = c;
            PUSH_I (result);
            break;
          }

#ifdef BH_SENSOR_PROFILE
        case JEFF_OP_MONITORENTER:
        case JEFF_OP_MONITOREXIT:
          (void)POP_R ();
          break;
#else
        case JEFF_OP_MONITORENTER:
          {
            JitReg obj = STACK_R (1);
            JitInsn *insn;

            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), obj, FRAME_IP ());

            gen_commit_for_gc (frame);
            if (!(insn = GEN_INSN (INVOKENATIVE, 0,
                                   NEW_INTRINSIC (jeff_sync_object_lock), 2)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = obj;

            (void)POP_R ();
            break;
          }

        case JEFF_OP_MONITOREXIT:
          {
            JitReg obj = POP_R ();
            JitInsn *insn;

            GEN_INSN_CHK (CHKNULL, CUR_IP_OFFSET (), obj, FRAME_IP ());

            gen_commit_for_gc (frame);
            if (!(insn = GEN_INSN (INVOKENATIVE, 0,
                                   NEW_INTRINSIC (jeff_sync_object_unlock), 2)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = obj;
            break;
          }
#endif

        case JEFF_OP_MULTIANEWARRAY:
          {
            JitReg array = jit_cc_new_reg_I4 (cc);
            JitReg d, c;
            int dim = read_uint8 (frame->ip);
            JitInsn *insn;

            read_jeff_descriptor (d, c, frame->ip, cur_class);
            /* The below commit also saves parameters required by the
               intrinsic function.  */
            gen_commit_for_all (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, array,
                                   NEW_INTRINSIC (jeff_interp_new_multiarray), 5)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = d;
            *(jit_insn_opndv (insn, 4)) = c;
            *(jit_insn_opndv (insn, 5)) = NEW_CONST (I4, dim);
            *(jit_insn_opndv (insn, 6)) = cc->fp_reg;
            POP (dim);
            PUSH_R (array);
            break;
          }

        case JEFF_OP_IFNULL:
          DEF_OPCODE_IFA (BEQ);
          break;

        case JEFF_OP_IFNONNULL:
          DEF_OPCODE_IFA (BNE);
          break;

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_IFNULL_W:
          DEF_OPCODE_IFA_W (BEQ);
          break;

        case JEFF_OP_IFNONNULL_W:
          DEF_OPCODE_IFA_W (BNE);
          break;
#endif

        case JEFF_OP_BREAKPOINT:
          UNSUPPORTED_OPCODE ();
          break;

        case JEFF_OP_NEWCONSTARRAY:
          {
            JitReg array = jit_cc_new_reg_I4 (cc);
            unsigned length;
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            JeffOffset offset;
#else
            JeffDOffset offset;
#endif
            JitReg d, c;
            JitInsn *insn;

            read_jeff_descriptor (d, c, frame->ip, cur_class);
            length = read_uint16_align (frame->ip);
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            offset = read_uint16 (frame->ip);
#else
            offset = read_uint32_align (frame->ip);
#endif
            gen_commit_for_gc (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, array,
                                   NEW_INTRINSIC (jeff_interp_new_constarray), 5)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = d;
            *(jit_insn_opndv (insn, 4)) = c;
            *(jit_insn_opndv (insn, 5)) = NEW_CONST (I4, length);
            *(jit_insn_opndv (insn, 6)) = NEW_REL (BCIP, NONE, offset, (uint32)cur_class + offset);
            PUSH_R (array);
            break;
          }

        case JEFF_OP_SLOOKUPSWITCH:
          {
            JeffOffset offset = read_uint16_align (frame->ip);
            unsigned pairs_num = read_uint16 (frame->ip), i;
            int16 *match_table = (int16 *)frame->ip;
            JeffOffset *jump_table = (JeffOffset *)(match_table + pairs_num);
            JitReg value = POP_I ();
            JitOpndLookupSwitch *opnd;
            JitInsn *insn;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (LOOKUPSWITCH, value, pairs_num)))
              break;

            opnd = jit_insn_opndls (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i < pairs_num; i++)
              {
                opnd->match_pairs[i].value = match_table[i];
                opnd->match_pairs[i].target = NEW_CONST
                  (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);
              }

            goto cleanup_and_return;
          }

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_SLOOKUPSWITCH_W:
          {
            JeffDOffset offset = read_uint32_align (frame->ip);
            unsigned pairs_num = read_uint16 (frame->ip), i;
            int16 *match_table = (int16 *)frame->ip;
            JeffDOffset *jump_table = (JeffDOffset *)align_uint (
                                            (unsigned)(match_table + pairs_num), 4);
            JitReg value = POP_I ();
            JitOpndLookupSwitch *opnd;
            JitInsn *insn;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (LOOKUPSWITCH, value, pairs_num)))
              break;

            opnd = jit_insn_opndls (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i < pairs_num; i++)
              {
                opnd->match_pairs[i].value = match_table[i];
                opnd->match_pairs[i].target = NEW_CONST
                  (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);
              }

            goto cleanup_and_return;
          }
#endif

        case JEFF_OP_STABLESWITCH:
          {
            JeffOffset offset = read_uint16_align (frame->ip);
            int32 low_value = read_int16 (frame->ip);
            int32 high_value = read_int16 (frame->ip), i;
            JeffOffset *jump_table = (JeffOffset *)frame->ip;
            JitReg value = POP_I ();
            JitOpndTableSwitch *opnd;
            JitInsn *insn;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (TABLESWITCH, value, low_value, high_value)))
              break;

            opnd = jit_insn_opndts (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i <= high_value - low_value; i++)
              opnd->targets[i] = NEW_CONST
                (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);

            goto cleanup_and_return;
          }

#if BEIHAI_ENABLE_JEFF_EXTENSION != 0
        case JEFF_OP_STABLESWITCH_W:
          {
            JeffDOffset offset = read_uint32_align (frame->ip);
            int32 low_value = read_int16 (frame->ip);
            int32 high_value = read_int16 (frame->ip), i;
            JeffDOffset *jump_table = (JeffDOffset *)frame->ip;
            JitReg value = POP_I ();
            JitOpndTableSwitch *opnd;
            JitInsn *insn;

            gen_commit_for_branch (frame);

            if (!(insn = GEN_INSN (TABLESWITCH, value, low_value, high_value)))
              break;

            opnd = jit_insn_opndts (insn);
            opnd->default_target = NEW_CONST
              (I4, (uint8 *)cur_class + offset - orig_ip);

            for (i = 0; i <= high_value - low_value; i++)
              opnd->targets[i] = NEW_CONST
                (I4, (uint8 *)cur_class + jump_table[i] - orig_ip);

            goto cleanup_and_return;
          }
#endif

        case JEFF_OP_IINC_W:
          {
            unsigned var_index;
            int inc_val;
            JitReg result;

            var_index = read_uint16_align (frame->ip);
            inc_val = read_int16 (frame->ip);
            GEN_INSN_NORM (I4, result, ADD, 0, LOCAL_I (var_index),
                           NEW_CONST (I4, inc_val));
            SET_LOCAL_I (var_index, result);
            break;
          }

        case JEFF_OP_CLDC:
          {
            JitReg d, c;
            JitReg obj = jit_cc_new_reg_I4 (cc);
            JitInsn *insn;

            read_jeff_descriptor (d, c, frame->ip, cur_class);
            gen_commit_for_gc (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, obj,
                                   NEW_INTRINSIC (jeff_interp_load_class), 2)))
              break;

            *(jit_insn_opndv (insn, 2)) = d;
            *(jit_insn_opndv (insn, 3)) = c;
            PUSH_R (obj);
            break;
          }

        case JEFF_OP_SLDC:
          jit_assert (0);
          break;

        case JEFF_OP_SLDC_INDEX:
          {
#if BEIHAI_ENABLE_JEFF_EXTENSION == 0
            unsigned index = read_uint16_align (frame->ip);
#else
            unsigned index = read_uint32_align (frame->ip);
#endif
            JitReg string = jit_cc_new_reg_I4 (cc);
            JitInsn *insn;

            gen_commit_for_gc (frame);

            if (!(insn = GEN_INSN (INVOKENATIVE, string,
                                   NEW_INTRINSIC (jeff_interp_load_string), 3)))
              break;

            *(jit_insn_opndv (insn, 2)) = cc->self_reg;
            *(jit_insn_opndv (insn, 3)) = NEW_REL (CLASS, NONE, 0, cur_class);
            *(jit_insn_opndv (insn, 4)) = NEW_CONST (I4, index);
            PUSH_R (string);
            break;
          }

        case JEFF_OP_ILDC:
          DEF_OPCODE_XLDC (I, I4);
          break;

        case JEFF_OP_LLDC:
          DEF_OPCODE_XLDC (L, I8);
          break;

        case JEFF_OP_FLDC:
          DEF_OPCODE_XLDC (F, F4);
          break;

        case JEFF_OP_DLDC:
          DEF_OPCODE_XLDC (D, F8);
          break;

        case JEFF_OP_DLOAD_W:
          PUSH_D (LOCAL_D (read_uint16_align (frame->ip)));
          break;

        case JEFF_OP_DSTORE_W:
          SET_LOCAL_D (read_uint16_align (frame->ip), POP_D ());
          break;

        case JEFF_OP_FLOAD_W:
          PUSH_F (LOCAL_F (read_uint16_align (frame->ip)));
          break;

        case JEFF_OP_FSTORE_W:
          SET_LOCAL_F (read_uint16_align (frame->ip), POP_F ());
          break;

        case JEFF_OP_ILOAD_W:
          PUSH_I (LOCAL_I (read_uint16_align (frame->ip)));
          break;

        case JEFF_OP_ISTORE_W:
          SET_LOCAL_I (read_uint16_align (frame->ip), POP_I ());
          break;

        case JEFF_OP_LLOAD_W:
          PUSH_L (LOCAL_L (read_uint16_align (frame->ip)));
          break;

        case JEFF_OP_LSTORE_W:
          SET_LOCAL_L (read_uint16_align (frame->ip), POP_L ());
          break;

        case JEFF_OP_ALOAD_W:
          PUSH_R (LOCAL_R (read_uint16_align (frame->ip)));
          break;

        case JEFF_OP_ASTORE_W:
          STORE_LOCAL_R (read_uint16_align (frame->ip));
          break;

        case JEFF_OP_INVOKEDYNAMIC:
          goto cleanup_and_return;

        case JEFF_OP_SWITCH_TO_JITED:
          {
#if BEIHAI_ENABLE_JIT_LLVM == 0
            /* It has been compiled, simply generate leave block. */
            goto gen_leave_and_return;
#else
            if (frame->ip - 1 != frame_orig_ip)
              {
                /* Continue to translate it for LLVM mode. */
                opcode = jit_region_find_entry (frame->ip - 1)->original_opcode;
                goto switch_again;
              }
#endif
          }
 gen_leave_and_return:
          {
            frame->ip--;
            orig_ip--;
            if (frame->ip == frame_orig_ip)
              {
                /* Give up compilation , avoid going into loop dead */
                orig_ip = NULL;
                goto cleanup_and_return;
              }
            else
              {
                gen_commit_for_branch (frame);
                GEN_INSN (JMP, NEW_CONST (I4, 0));
                goto cleanup_and_return;
              }
          }

        default:
          /* printf ("unsupported opcode : 0x%x\n", opcode); */
          UNSUPPORTED_OPCODE ();
        }

      if (jit_get_error () == JIT_ERROR_OOM)
        {
          orig_ip = NULL;
          goto cleanup_and_return;
        }
    }

 cleanup_and_return:
  *(jit_annl_end_sp (cc, jit_block_label (block))) = frame->sp - frame->lp;

  return orig_ip;
}

static void
gen_init_refs (JitCompContext *cc, JitBlock *block,
               JeffMethodLinked *method, int cell_num,
               JitReg cur_fp)
{
  unsigned ref_offset = offsetof (JeffInterpFrame, lp) + cell_num * 4;
  int i, j, k;
  const uint8 *desc;
  int argnum;
  union
  {
    uint32 uint32_val;
    uint8  uint8_val[4];
  } ref_val;

  desc = jeff_get_method_descriptor (method);
  argnum = *(uint16 *)desc;
  desc += 2;
  ref_val.uint32_val = 0;
  j = 0;

  if (!(method->access_flag & JEFF_ACC_STATIC))
    ref_val.uint8_val[j++] = 1;

  for (i = 0, k = 0; i < argnum; i++)
    {
      JeffDescriptor *d = (JeffDescriptor *)desc;
      jit_assert (j >= 0 && j < 4);

      if ((d->type & JEFF_TYPE_REF))
        ref_val.uint8_val[j++] = 1;
      else if ((d->type & JEFF_TYPE_TWO_CELL))
        j += 2;
      else
        j++;

      if (j >= 4)
        {
          /* TODO: consider the case that the compiling machine has a
             different byte order with the target machine.  Currently,
             assume that they are the same.  */
          GEN_INSN (STI4, NEW_CONST (I4, ref_val.uint32_val),
                    cur_fp, NEW_CONST (I4, ref_offset + k));
          j -= 4;
          k += 4;
          ref_val.uint32_val = 0;
        }

      desc += jeff_descriptor_size (d);
    }

  for (; k < cell_num; k += 4)
    {
      GEN_INSN (STI4, NEW_CONST (I4, ref_val.uint32_val),
                cur_fp, NEW_CONST (I4, ref_offset + k));
      ref_val.uint32_val = 0;
    }
}

static Frame*
init_region_translation (JitCompContext *cc, JitHotEntry *entry)
{
  JeffMethodLinked *method = (JeffMethodLinked *)entry->method;
  const JeffBytecodeBlock *code = jeff_get_method_code (method);
  const unsigned cell_num = code->max_locals + code->max_stack;
  Frame *frame;

  if (!(frame = jit_calloc (offsetof (Frame, lp)
                            + sizeof (*frame->lp) * cell_num)))
    return NULL;

  frame->cur_method = method;
  frame->cur_class = jeff_get_method_class (method);
  frame->max_locals = code->max_locals;
  frame->max_stack = code->max_stack;
  frame->cc = cc;
  cc->pass_local_data = frame;
  cc->interp_frame_size = jeff_interp_interp_frame_size (cell_num);
  cc->total_frame_size = jeff_interp_total_frame_size (cell_num);
#if BEIHAI_ENABLE_JIT != 0
  cc->jited_return_address_offset = offsetof (JeffInterpFrame,
                                              jited_return_address);
#endif

  if (entry->bcip == code->bytecode)
    /* This is a region whose entry is the method's entry,
       generate the method prolog for it.  */
    {
      JitBlock *block = frame->block = jit_cc_entry_block (cc);
      unsigned frame_size = jeff_interp_total_frame_size (cell_num);
      unsigned outs_size = jeff_interp_outs_offset (code->max_stack);
      JitReg top = jit_cc_new_reg_I4 (cc);
      JitReg boundary = jit_cc_new_reg_I4 (cc);
      JitReg new_top = jit_cc_new_reg_I4 (cc);
      JitReg frame_boundary = jit_cc_new_reg_I4 (cc);
      JitReg lp = jit_cc_new_reg_I4 (cc);

      /* Set the SP explicitly because in async method mode, the SP
         may not be correct as the bcip of entry is modified but SP is
         not.  */
      entry->sp = code->max_locals;
      /* runtime/jeff/jeff-interp.c::ALLOC_FRAME */
      /* Don't use GEN_INSN_NORM in this block.  Otherwise, the
         jit_cc_reset_insn_hash must be called after generating
         instructions for this block.  */
      GEN_INSN (LDI4, top, cc->self_reg,
                NEW_CONST (I4, offsetof (JeffThread,
                                         java_stack.s.top)));
      GEN_INSN (LDI4, boundary, cc->self_reg,
                NEW_CONST (I4, offsetof (JeffThread,
                                         java_stack.s.top_boundary)));
      GEN_INSN (ADD, frame_boundary, top, NEW_CONST (I4, frame_size + outs_size));
      GEN_INSN (CHKSOE, NEW_CONST (I4, 0), frame_boundary, boundary, FRAME_IP ());
      /* Add first and then sub to reduce one used register.  */
      GEN_INSN (SUB, new_top, frame_boundary, NEW_CONST (I4, outs_size));
      GEN_INSN (STI4, new_top, cc->self_reg,
                NEW_CONST (I4, offsetof (JeffThread,
                                         java_stack.s.top)));
      /* Set frame->sp = frame->lp, in case of GC in jeff_sync_object_lock */
      GEN_INSN (ADD, lp, top, NEW_CONST (I4, offsetof (JeffInterpFrame, lp)));
      GEN_INSN (STI4, lp, top, NEW_CONST (I4, offsetof (JeffInterpFrame, sp)));
      GEN_INSN (STI4, cc->fp_reg, top,
                NEW_CONST (I4, offsetof (JeffInterpFrame, prev_frame)));

      /* runtime/jeff/jeff-interp.c::CALL_METHOD_EPILOGUE */
      GEN_INSN (STI4, NEW_REL (METHOD, NONE, 0, method), top,
                NEW_CONST (I4, offsetof (JeffInterpFrame, method)));
      gen_init_refs (cc, block, method, cell_num, top);
      GEN_INSN (STI4, top, cc->self_reg,
                NEW_CONST (I4, offsetof (JeffThread, cur_frame)));
      GEN_INSN (MOV, cc->fp_reg, top);

#if BEIHAI_ENABLE_INTERP_PROFILER != 0 || BEIHAI_ENABLE_INTERP_PROFILER_METHOD != 0
      /* frame->start_time = 0 */
      GEN_INSN (STI4, NEW_CONST (I4, 0), cc->fp_reg,
                NEW_CONST (I4, offsetof (JeffInterpFrame, start_time)));
#endif

      if (method->access_flag & JEFF_ACC_SYNCHRONIZED)
        {
          JitInsn *insn;
          JitReg obj = jit_cc_new_reg_I4 (cc);

          if (method->access_flag & JEFF_ACC_STATIC)
            {
              if (!(insn = GEN_INSN (INVOKENATIVE, obj,
                      NEW_INTRINSIC (jeff_runtime_get_class_object), 1)))
                {
                  jit_free (frame);
                  return NULL;
                }

              *(jit_insn_opndv (insn, 2)) = NEW_REL (CLASS, NONE, 0, frame->cur_class);
            }
          else
            GEN_INSN (LDI4, obj, cc->fp_reg, NEW_CONST (I4, offset_of_local (0)));

          if (!(insn = GEN_INSN (INVOKENATIVE, 0,
                  NEW_INTRINSIC (jeff_sync_object_lock), 2)))
            {
              jit_free (frame);
              return NULL;
            }

          *(jit_insn_opndv (insn, 2)) = cc->self_reg;
          *(jit_insn_opndv (insn, 3)) = obj;
        }
    }

  return frame;
}

JitBlock*
jit_frontend_jeff_translate_block (JitCompContext *cc, JitHotEntry *entry,
                                   JitBitmap *is_reached)
{
  JitBlock *block;
  JitReg label;
  uint8 *end;
  Frame *frame = (Frame *)cc->pass_local_data;
  ValueSlot *sp;

  if (!entry)
    /* Clean up the pass local data.  */
    {
      jit_free (cc->pass_local_data);
      cc->pass_local_data = NULL;
      return NULL;
    }

  if (!frame)
    /* It's the first time calling this pass, do initialization.  */
    if (!(frame = init_region_translation (cc, entry)))
      return NULL;

  jit_assert (entry->sp >= frame->max_locals);
  frame->sp = frame->lp + entry->sp;
  frame->ip = entry->bcip;
  memset (frame->lp, 0,
          sizeof (*frame->lp) * (frame->max_locals + frame->max_stack));
  frame->committed_sp = NULL;
  frame->committed_ip = NULL;

  for (sp = frame->sp;
       sp < frame->lp + frame->max_locals + frame->max_stack;
       sp++)
    /* Reference flags of slots above top of the working stack are
       always 0.  */
    sp->committed_ref = 1 + 0;

  if (!(frame->block = block = jit_cc_new_block (cc, 0))
      || !(end = translate (cc, block, frame, is_reached)))
    return NULL;

  label = jit_block_label (block);
  *(jit_annl_begin_bcip (cc, label)) = entry->bcip;
  *(jit_annl_end_bcip (cc, label)) = end;

  return block;
}

JitBlock*
jit_frontend_jeff_gen_leaving_block (JitCompContext *cc, void *bcip,
                                     unsigned sp_offset)
{
  JitBlock *block;

  if (!(block = jit_cc_new_block (cc, 0)))
    return NULL;

  *(jit_annl_begin_bcip (cc, jit_block_label (block))) = bcip;
  GEN_INSN (LEAVE, NEW_CONST (I4, JIT_INTERP_ACTION_NORMAL),
            NEW_CONST (I4, jit_frontend_jeff_bcip_to_offset (cc->method, bcip)),
            NEW_CONST (I4, offset_of_local (sp_offset)));

  return jit_get_error () == JIT_ERROR_OOM ? NULL : block;
}

void
jit_frontend_jeff_replace_opcode (void *ip)
{
  *(uint8 *)ip = JEFF_OP_SWITCH_TO_JITED;
}

uint8*
jit_frontend_jeff_method_begin_bcip (void *method)
{
  return (jeff_get_method_code (method))->bytecode;
}

uint8*
jit_frontend_jeff_method_end_bcip (void *method)
{
  JeffBytecodeBlock *code = jeff_get_method_code (method);
  return code->bytecode + code->bytecode_size;
}

void**
jit_frontend_jeff_method_jited_code (void *method)
{
  return &((JeffMethodLinked *)method)->jited_code;
}

static void *
jeff_method_jited_code (JeffMethodLinked *method)
{
  return method->jited_code;
}

bool
jit_frontend_jeff_is_region_entry (void *method, void *bcip)
{
  JeffMethodLinked *jeff_method = (JeffMethodLinked *)method;
  JeffBytecodeBlock *code = jeff_get_method_code (jeff_method);
  const uint8 *jeff_bcip = (uint8 *)bcip;

  return (code->bytecode == jeff_bcip
          ? jeff_method_jited_code (jeff_method) != jit_globals.call_to_interp_from_jited
          : *jeff_bcip == JEFF_OP_SWITCH_TO_JITED);
}

void
jit_frontend_jeff_print_method_name (void *method)
{
  jeff_print_method_qname (method);
}

unsigned
jit_frontend_jeff_get_method_name (void *method, char *buf,
                                   unsigned buf_len)
{
  JeffMethodLinked *m = (JeffMethodLinked *)method;
  JeffClassHeaderLinked *clz = jeff_get_method_class (m);
  JeffFileHeaderLinked *file = jeff_get_file_header (clz);
  const JeffString *pname = jeff_get_class_pname (clz);
  const JeffString *cname = jeff_get_class_cname (clz);
  const JeffString *mname = jeff_get_method_name (m);
  unsigned len = (jeff_get_mangled_qname_length (pname, cname, mname)
                  + 2           /* "__" */
                  + (jeff_get_mangled_method_descriptor_length
                     (jeff_get_method_descriptor (m), file, NULL)));
  char *p = buf;

  if (buf_len >= len)
    {
      p = jeff_get_mangled_qname (p, pname, cname, mname);
      *p++ = '_';
      *p++ = '_';
      jeff_get_mangled_method_descriptor (p, jeff_get_method_descriptor (m),
                                          file);
    }

  return len;
}

unsigned
jit_frontend_jeff_bcip_to_offset (void *method, void *bcip)
{
  return bcip ? (uint8 *)bcip - (uint8 *)jeff_get_method_class (method) : 0;
}

unsigned
jit_frontend_thread_jit_cache_offset ()
{
#if BEIHAI_ENABLE_JIT != 0
  return offsetof (JeffThread, jit_cache);
#else
  return 0;
#endif
}

bool
jit_frontend_jeff_call_code_filter (JitCodeFilter filter,
                                    void *method, void *bcip)
{
  const JeffMethodLinked *m = method;
  const JeffClassHeaderLinked *c = jeff_get_method_class (m);
  const JeffString *pname = jeff_get_class_pname (c);
  const JeffString *cname = jeff_get_class_cname (c);
  const JeffString *mname = jeff_get_method_name (m);

  return (*filter) (pname->value, pname->length,
                    cname->value, cname->length,
                    mname->value, mname->length,
                    jit_frontend_jeff_bcip_to_offset (method, bcip));
}

void
jit_frontend_jeff_suspend_all ()
{
  jeff_runtime_suspend_all ();
}

void
jit_frontend_jeff_resume_all ()
{
  jeff_runtime_resume_all ();
}

void
jit_frontend_jeff_enumerate_code ()
{
  jeff_runtime_enumerate_code ();
}

void
jit_frontend_jeff_enter_safe_state ()
{
  jeff_runtime_enter_safe_state ();
}

void
jit_frontend_jeff_exit_safe_state ()
{
  jeff_runtime_exit_safe_state ();
}

bool
jit_frontend_jeff_aot_fill_header (JitAotRegionHeader *region_header,
                                   const void *package, void *method,
                                   void *bcip)
{
  const JeffFileHeaderLinked *file = (JeffFileHeaderLinked *)package;

  if (method)
    {
      if (!jeff_is_addr_in_file (file, method))
        return false;

      jit_assert (!bcip);
      bcip = (jeff_get_method_code ((JeffMethodLinked *)method))->bytecode;
    }
  else
    {
      if (!jeff_is_addr_in_file (file, bcip))
        return false;

      jit_assert (jeff_find_method_of_bcip (file, (uint8 *)bcip));
    }

  /* Store the file offset of bcip to the region header.  */
  region_header->bcip = (uint8 *)bcip - (uint8 *)package;

  return true;
}

void
jit_frontend_jeff_aot_parse_header (const JitAotRegionHeader *region_header,
                                    const void *package, void **method,
                                    void **bcip)
{
  *bcip = (uint8 *)package + region_header->bcip;
  *method = jeff_find_method_of_bcip
    ((JeffFileHeaderLinked *)package, *bcip);
  /* This shoudn't happen due to the integrity check.  */
  jit_assert (*method);
}

uint32
jit_frontend_jeff_aot_reloc_value (const void *method, uint32 reloc_info)
{
  return jit_frontend_jeff_aot_reloc_value_lower (method, reloc_info);
}
