#include "cg/cg-intrinsic-func.h"
#include "cg/cg-intrinsic.h"

#include "jit-ir.h"
#include "jit-region.h"

#include "jit-export.h"
#include "jit-compiler.h"
#include "jit-aot.h"
#include "jit-codegen.h"
#include "jit-codecache.h"
#include "jit-dump.h"
#include "jit-export.h"
#include "libenc/encoder.h"
#include "libenc/encoder_defs_ia32.h"
#include "libenc/dec_base.h"
#include "jit-profiler.h"
#include "jit-frontend.h"
#include "bh_log.h"
/* Dump insn and its lower result of native code */
/* #define CODEGEN_DUMP_LOWER_RESULT  1 */

/* Dump lower binary */
/* #define CODEGEN_DUMP_LOWER_BINARY 1 */

/* Dump insn and its execution result of native code */
/*#define CODEGEN_TRACE_EXEC_RESULT   1*/

/* Check the arguments of insn or not */
/*#define CODEGEN_CHECK_ARGS  1*/

/* Enable float/double support or not */
#define CODEGEN_ENABLE_FLOATING_POINT   1

#define BREAK break
#define PRINT_LINE LOG_VERBOSE ("<Line:%d>\n", __LINE__);

#ifdef CODEGEN_DUMP_LOWER_RESULT
#define GOTO_FAIL   \
  do {              \
    PRINT_LINE;     \
    goto fail;      \
  } while (0)
#else
#define GOTO_FAIL   \
  goto fail
#endif

#define JIT_CACHE_OFFSET jit_frontend_thread_jit_cache_offset()

#define m_from_jit_cache(m) do {                    \
    m_from_b_d (m, esp_reg, 16 + 4); /* self */     \
    mov_r_m (reg_I4_free, m);                       \
    m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free),\
                JIT_CACHE_OFFSET);                  \
  } while (0)

#define SZ_I8   sizeof (int64)
#define SZ_I4   sizeof (int32)
#ifdef CODEGEN_ENABLE_FLOATING_POINT
#define SZ_F4   sizeof (float)
#define SZ_F8   sizeof (double)

#define int64_min ((int64) 1 << 63)
#define int64_max (~((int64) 1 << 63))
#define int32_min ((int32) 1 << 31)
#define int32_max (~((int32) 1 << 31))

static void
int64_from_float (union_cache *uc)
{
  if (uc->f >= int64_max)
    uc->l = int64_max;
  else if (uc->f <= int64_min)
    uc->l = int64_min;
  else if (uc->f != uc->f)
    uc->l = 0;
  else
    uc->l = (int64) uc->f;
}

static int32
int32_from_float (union_cache *uc)
{
  if (uc->f >= int32_max)
    return int32_max;
  else if (uc->f <= int32_min)
    return int32_min;
  else if (uc->f != uc->f)
    return 0;
  else
    return (int32) uc->f;
}

static void
int64_from_double (union_cache *uc)
{
  if (uc->d >= int64_max)
    uc->l = int64_max;
  else if (uc->d <= int64_min)
    uc->l = int64_min;
  else if (uc->d != uc->d)
    uc->l = 0;
  else
    uc->l = (int64) uc->d;
}

static int32
int32_from_double (union_cache *uc)
{
  if (uc->d >= int32_max)
    return int32_max;
  else if (uc->d <= int32_min)
    return int32_min;
  else if (uc->d != uc->d)
    return 0;
  else
    return (int32) uc->d;
}

static void
float_rem (union_cache *uc)
{
  uc->uf.f1 = fmodf(uc->uf.f1, uc->uf.f2);
}

static void
double_rem (union_cache *uc)
{
  uc->ud.d1 = fmod(uc->ud.d1, uc->ud.d2);
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

#if BEIHAI_ENABLE_JIT_LLVM == 0
/**
 * Fill the native code of the begin code block,
 * push registers needed to save, and load the params
 *
 * @param frame current java frame's start address, will be stored in ebp
 */
#ifdef CODEGEN_ENABLE_FLOATING_POINT
#define ENCODER_FILL_START()                            \
  do {                                                  \
    M_Opnd _m;                                          \
    Imm_Opnd _imm;                                      \
    stream = nop (stream);  /* nop */                   \
    push_r (ebx);           /* push ebx */              \
    push_r (esi);           /* push esi */              \
    push_r (edi);           /* push edi */              \
    push_r (ebp);           /* push ebp */              \
    m_from_b_d (_m, esp_reg, 16 + 4); /* self */        \
    mov_r_m (ebx, _m);      /* mov ebx, [esp + 20] */   \
    m_from_b_d (_m, esp_reg, 16 + 8);/* info */         \
    mov_r_m (esi, _m);      /* mov esi, [esp + 24] */   \
    m_from_b_d (_m, esi_reg, 0);                        \
    mov_r_m (ebp, _m);                                  \
    m_from_b_d (_m, esi_reg, 4);                        \
    mov_r_m (ecx, _m);                                  \
    m_from_b_d (_m, esi_reg, 8);                        \
    mov_r_m (edx, _m);                                  \
                                                        \
    finit();                                            \
    /* load st0 from fval[0] or fval[0-1] */            \
    /* check self->last_return_type */                  \
    m_from_b_d (_m, esi_reg, 20);                       \
    /* return_type == JEFF_INTERP_RETURN_SIZE_8(2) ? */ \
    imm_from_sz_v_s (_imm, SZ32, 2, true);              \
    alu_m_imm (cmp, _m, _imm);                          \
    imm_from_sz_v_s (_imm, SZ8, 7, true);               \
    je (_imm);                                          \
    /* return_type != 2, st0 = fval[0] */               \
    m_from_b_d (_m, esi_reg, 12);                       \
    fmov_r_m(0, _m);                                    \
    imm_from_sz_v_s (_imm, SZ8, 5, true);               \
    jmp_imm (_imm);                                     \
    /* return_type == 2, st0 = fval[0-1] */             \
    m_from_b_d (_m, esi_reg, 12);                       \
    dmov_r_m(0, _m);                                    \
                                                        \
    /* jump to target */                                \
    m_from_b_d (_m, esp_reg, 16 + 12);                  \
    jmp_m (_m);                                         \
  } while (0)
#else
#define ENCODER_FILL_START()                            \
  do {                                                  \
    M_Opnd _m;                                          \
    stream = nop (stream);  /* nop */                   \
    push_r (ebx);           /* push ebx */              \
    push_r (esi);           /* push esi */              \
    push_r (edi);           /* push edi */              \
    push_r (ebp);           /* push ebp */              \
    m_from_b_d (_m, esp_reg, 16 + 4); /* self */        \
    mov_r_m (ebx, _m);      /* mov ebx, [esp + 20] */   \
    m_from_b_d (_m, esp_reg, 16 + 8);/* info */         \
    mov_r_m (esi, _m);      /* mov esi, [esp + 24] */   \
    m_from_b_d (_m, esi_reg, 0);                        \
    mov_r_m (ebp, _m);                                  \
    m_from_b_d (_m, esi_reg, 4);                        \
    mov_r_m (ecx, _m);                                  \
    m_from_b_d (_m, esi_reg, 8);                        \
    mov_r_m (edx, _m);                                  \
                                                        \
    /* jump to target */                                \
    m_from_b_d (_m, esp_reg, 16 + 12);                  \
    jmp_m (_m);                                         \
  } while (0)
#endif

/**
 * Fill the ending of native code of an function,
 * resore stack(ebp) and pre-saved registers, and return to the caller
 */
#define ENCODER_FILL_END()                              \
  do {                                                  \
    finit();                                            \
    pop_r (ebp);            /* pop ebp */               \
    pop_r (edi);            /* pop edi */               \
    pop_r (esi);            /* pop esi */               \
    pop_r (ebx);            /* pop ebx */               \
    stream = ret1 (stream); /* ret */                   \
  } while (0)
#else /* else of BEIHAI_ENABLE_JIT_LLVM */
#define ENCODER_FILL_START()                            \
  do {                                                  \
    M_Opnd _m;                                          \
    Imm_Opnd _imm;                                      \
    stream = nop (stream);  /* nop */                   \
    push_r (ebx);           /* push ebx */              \
    push_r (esi);           /* push esi */              \
    push_r (edi);           /* push edi */              \
    push_r (ebp);           /* push ebp */              \
    m_from_b_d (_m, esp_reg, 16 + 4); /* self */        \
    mov_r_m (ebx, _m);      /* mov ebx, [esp + 20] */   \
    m_from_b_d (_m, esp_reg, 16 + 8);/* info */         \
    mov_r_m (esi, _m);      /* mov esi, [esp + 24] */   \
    m_from_b_d (_m, esi_reg, 0);                        \
    mov_r_m (ebp, _m);                                  \
  } while (0)

#define ENCODER_FILL_END()                              \
  do {                                                  \
    pop_r (ebp);            /* pop ebp */               \
    pop_r (edi);            /* pop edi */               \
    pop_r (esi);            /* pop esi */               \
    pop_r (ebx);            /* pop ebx */               \
    stream = ret1 (stream); /* ret */                   \
  } while (0)
#endif

/**
 * List of all int32 register operands except esp,
 * the element index is equal to the register no of I4 operand,
 * ebp = i0; eax, ebx, ecx, edx = i1 to i4; edi = i5;
 * and esi is free for code-gen to use
 */
static R_Opnd regs_I4[7];   /* { ebp, eax, ebx, ecx, edx, edi, esi } */
/* free int32 register operand, currently it is esi */
static R_Opnd reg_I4_free;  /* { esi } */

/**
 * The index of ebp/eax/ebx/ecx/edx/edi/esi registers
 * in regs_I4 array
 */
typedef enum {
  REG_EBP_INDEX,
  REG_EBX_INDEX,
  REG_EAX_INDEX,
  REG_ECX_INDEX,
  REG_EDX_INDEX,
  REG_EDI_INDEX,
  REG_ESI_INDEX,
  REG_I4_FREE_INDEX =  REG_ESI_INDEX
} RegIndexI4;


#ifdef CODEGEN_TRACE_EXEC_RESULT

#include <stdio.h>

/**
 * Dump all int32 registers' value
 *
 * @param r_eax value of register eax
 * @param r_ebx value of register ebx
 * @param r_ecx value of register ecx
 * @param r_edx value of register edx
 * @param r_edi value of register edi
 * @param r_esi value of register esi
 * @param r_ebp value of register ebp
 * @param r_esp value of register esp
 */
static void
dump_regs_I4 (int32 r_eax, int32 r_ebx, int32 r_ecx, int32 r_edx,
              int32 r_edi, int32 r_esi, int32 r_ebp, int32 r_esp)
{
  LOG_VERBOSE ("\nI4 Register values:\n");
  LOG_VERBOSE ("eax:%08X, ebx:%08X, ecx:%08X, edx:%08X, ",
          r_eax, r_ebx, r_ecx, r_edx);
  LOG_VERBOSE ("edi:%08X, esi:%08X, ebp:%08X, esp:%08X\n",
          r_edi, r_esi, r_ebp, r_esp);
}

/**
 * Retrieve the operand's number of an insn
 *
 * @param opcode the opcode of insn
 * @return the operands's number
 */
static int32
get_insn_opnd_num (int32 opcode)
{
  switch (opcode)
    {
      #define INSN(NAME, OPND_KIND, OPND_NUM)       \
      case JIT_OP_##NAME:                           \
        return OPND_NUM;

      #include "jit-ir.def"
      #undef INSN
    }
  return 0;
}

/**
 * Dump opcode
 *
 * @param opcode the opcode to dump
 */
static void
dump_insn_opcode(int32 opcode)
{
  switch (opcode)
    {
      #define INSN(NAME, OPND_KIND, OPND_NUM)       \
      case JIT_OP_##NAME:                           \
        LOG_VERBOSE ("\n  %-15s", #NAME);                \
        break;

      #include "jit-ir.def"
      #undef INSN
    }
}

/**
 * Dump register operand
 *
 * @param kind the kind of register
 * @param no the no of register
 */
static void
dump_insn_reg(int32 kind, int32 no)
{
  if (kind==JIT_REG_KIND_I4)
    LOG_VERBOSE (" i%d", no);
  else if (kind==JIT_REG_KIND_L4)
    LOG_VERBOSE (" L%d", no);
  else if (kind==JIT_REG_KIND_VOID)
    LOG_VERBOSE (" VOID");
}

/**
 * Dump a char
 *
 * @param ch the char to dump
 */
static void
dump_insn_char(int32 ch)
{
  LOG_VERBOSE ("%c", (char)ch);
}

/**
 * Dump a const value
 *
 * @param value the value to dump
 */
static void
dump_insn_const(uint32 value)
{
  LOG_VERBOSE (" 0x%x", value);
}

/**
 * Dump register status: index and value
 *
 * @param index the index of register
 * @param value the value of register
 */
static void
dump_reg(int32 index, uint32 value)
{
  LOG_VERBOSE ("    i%d:%08X ", index, value);
}

/* Push all registers before dumping insn info */
#define PUSH_ALL()  \
  do {              \
    push_r (eax);   \
    push_r (ebx);   \
    push_r (ecx);   \
    push_r (edx);   \
    push_r (edi);   \
    push_r (esi);   \
  } while (0)

/* Pop all registers after dumping insn info */
#define POP_ALL()   \
  do {              \
    pop_r (esi);    \
    pop_r (edi);    \
    pop_r (edx);    \
    pop_r (ecx);    \
    pop_r (ebx);    \
    pop_r (eax);    \
  } while (0)

/* Dump all int32 registers' status */
#define DUMP_REGS_I4()                                          \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    push_r (esp);                                               \
    push_r (ebp);                                               \
    push_r (esi);                                               \
    push_r (edi);                                               \
    push_r (edx);                                               \
    push_r (ecx);                                               \
    push_r (ebx);                                               \
    push_r (eax);                                               \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_regs_I4, true);    \
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 32, true);                     \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0);

/* Dump an int32 register's status */
#define DUMP_REG(index)                                         \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    if (0<=index && index <= 5)                                 \
      push_r (regs_I4[index]);                                  \
    else if (index == 6)                                        \
      push_r (reg_I4_free);                                     \
    else                                                        \
      push_r (esp);                                             \
    imm_from_sz_v_s (_imm, SZ32, index, true);                  \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_reg, true);        \
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 8, true);                      \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0)

/* Dump insn expression: dump register operand's info, such as i0, L1 etc. */
#define DUMP_INSN_REG(kind, no)                                 \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    imm_from_sz_v_s (_imm, SZ32, no, true);                     \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, kind, true);                   \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_insn_reg, true);   \
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 8, true);                      \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0)

/* Dump insn expression: dump a char, such as ',', '\n', ' ', etc. */
#define DUMP_INSN_CHAR(ch)                                      \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    imm_from_sz_v_s (_imm, SZ32, (int32)ch, true);              \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_insn_char, true);  \
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 4, true);                      \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0)

/* Dump insn expression: dump const value */
#define DUMP_INSN_CONST(data)                                   \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    imm_from_sz_v_s (_imm, SZ32, (int32)data, true);            \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_insn_const, true); \
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 4, true);                      \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0)

/* Dump insn expression: dump opcode */
#define DUMP_INSN_OPCODE(opcode)                                \
  do {                                                          \
    Imm_Opnd _imm;                                              \
                                                                \
    PUSH_ALL ();                                                \
    imm_from_sz_v_s (_imm, SZ32, (int32)opcode, true);          \
    push_imm (_imm);                                            \
    imm_from_sz_v_s (_imm, SZ32, (int32)dump_insn_opcode, true);\
    mov_r_imm (reg_I4_free, _imm);                              \
    call_r (reg_I4_free);                                       \
    imm_from_sz_v_s (_imm, SZ32, 4, true);                      \
    alu_r_imm (add, esp, _imm);                                 \
    POP_ALL ();                                                 \
  } while (0)


#define DUMP_INSN_LABEL(label_index)                            \
  do {                                                          \
    DUMP_INSN_CHAR ('\n');                                      \
    DUMP_INSN_CHAR ('L');                                       \
    DUMP_INSN_CHAR ('0' + label_index);                         \
    DUMP_INSN_CHAR (':');                                       \
    DUMP_INSN_CHAR ('\n');                                      \
  } while (0)

/* Dump insn expression and dump the related registers' value */
#define DUMP_INSN(cc, insn)                                             \
  do {                                                                  \
    int32 _opnd_num = get_insn_opnd_num (insn->opcode);                 \
    JitReg _r[4];                                                       \
    int32 _i;                                                           \
                                                                        \
    DUMP_INSN_OPCODE(insn->opcode);                                     \
    if (insn->opcode == JIT_OP_TABLESWITCH ||                           \
        insn->opcode == JIT_OP_LOOKUPSWITCH ||                          \
        insn->opcode == JIT_OP_CALLNATIVE)                              \
      {                                                                 \
        DUMP_INSN_CHAR ('\n');                                          \
        break;                                                          \
      }                                                                 \
    for (_i = 0; _i < _opnd_num; _i++)                                  \
      {                                                                 \
        _r[_i] = *jit_insn_opnd (insn, _i);                             \
        if (jit_reg_kind (_r[_i]) == JIT_REG_KIND_VOID ||               \
            jit_reg_kind (_r[_i]) == JIT_REG_KIND_L4)                   \
          DUMP_INSN_REG (jit_reg_kind (_r[_i]), jit_reg_no (_r[_i]));   \
        else if (!jit_reg_is_const (_r[_i]))                            \
          DUMP_INSN_REG(jit_reg_kind (_r[_i]), jit_reg_no (_r[_i]));    \
        else                                                            \
          DUMP_INSN_CONST((int32)jit_cc_get_const_I4 (cc, _r[_i]));     \
        if (_i != _opnd_num - 1)                                        \
          DUMP_INSN_CHAR(',');                                          \
      }                                                                 \
    DUMP_INSN_CHAR ('\n');                                              \
    for (_i = 0; _i < _opnd_num; _i++)                                  \
      if (jit_reg_kind (_r[_i]) == JIT_REG_KIND_I4 &&                   \
          !jit_reg_is_const (_r[_i]))                                   \
        {                                                               \
          DUMP_REG (jit_reg_no (_r[_i]));                               \
          DUMP_INSN_CHAR ('\n');                                        \
        }                                                               \
  } while (0)

#endif /* end of CODEGEN_TRACE_EXEC_RESULT */

#define MAX_CODE_BLOCK_SIZE 128

static char *code_block_switch_to_jited_from_interp = NULL;
static char *code_block_switch_to_interp_from_jited = NULL;
static char *code_block_switch_to_interp_from_jited_soe = NULL;
static char *code_block_switch_to_interp_from_jited_ae = NULL;
static char *code_block_switch_to_interp_from_jited_npe = NULL;
static char *code_block_switch_to_interp_from_jited_aioobe = NULL;
static char *code_block_switch_to_interp_from_jited_thrown = NULL;
static char *code_block_call_to_interp_from_jited = NULL;
static char *code_block_return_to_interp_from_jited = NULL;

/**
 * Backend dependent relocation record.
 */
typedef struct AotRelocRecord
{
  /* The relocation type: 1, 2, 4: replace 1, 2 or 4 bytes with the
     value retrieved from frontend; 0: treat the relocation data as
     index to the glue code blocks.  */
  unsigned relocation_type : 8;

  /* Offset to the position that need to be modified.  */
  unsigned offset : 24;

  /* The relocation data.  */
  uint32 relocation_data;
} AotRelocRecord;

#define AOT_RELOC_JMP_TARGET_CODE   0x10
#define AOT_RELOC_CODE_BLOCK        0x20
#define AOT_RELOC_RETURN_ADDRESS    0x40

#define AOT_RELOC_RECORD_NUM        512

/* Records for one compilation.  */
static AotRelocRecord aot_reloc_records[AOT_RELOC_RECORD_NUM];

/* The current index to the aot_reloc_record array.  */
static unsigned cur_aot_reloc_record_index;

/**
 * Add a relocation record to the table.
 *
 * @param type relocation type
 * @param offset offset to the code stream
 * @param reloc_data relocation data
 */
static void
add_aot_reloc_record (unsigned type, unsigned offset, unsigned reloc_data)
{
  if (cur_aot_reloc_record_index < AOT_RELOC_RECORD_NUM)
    {
      unsigned i = cur_aot_reloc_record_index++;
      aot_reloc_records[i].relocation_type = type;
      aot_reloc_records[i].offset = offset;
      aot_reloc_records[i].relocation_data = reloc_data;
    }
}

static char*
interp_action_to_code_block (unsigned action)
{
  switch (action)
    {
    case JIT_INTERP_ACTION_NORMAL:
      return code_block_switch_to_interp_from_jited;
    case JIT_INTERP_ACTION_SOE:
      return code_block_switch_to_interp_from_jited_soe;
    case JIT_INTERP_ACTION_AE:
      return code_block_switch_to_interp_from_jited_ae;
    case JIT_INTERP_ACTION_NPE:
      return code_block_switch_to_interp_from_jited_npe;
    case JIT_INTERP_ACTION_AIOOBE:
      return code_block_switch_to_interp_from_jited_aioobe;
    case JIT_INTERP_ACTION_THROWN:
      return code_block_switch_to_interp_from_jited_thrown;
    }

  jit_assert (0);
  return NULL;
}

static bool
check_aot_reloc_records (const uint8 *code, const void *method)
{
  unsigned i, cur_ip, val;

  if (!jit_globals.options.aot_gen_mode)
    return true;

  for (i = 0; i < cur_aot_reloc_record_index; i++) {
    switch (aot_reloc_records[i].relocation_type & 0x0f)
      {
      case 1:
        jit_assert (jit_frontend_aot_reloc_value
                    (method, aot_reloc_records[i].relocation_data)
                    == *(code + aot_reloc_records[i].offset));
        break;

      case 2:
        jit_assert (jit_frontend_aot_reloc_value
                    (method, aot_reloc_records[i].relocation_data)
                    == *(uint16 *)(code + aot_reloc_records[i].offset));
        break;

      case 4:
        if ((aot_reloc_records[i].relocation_type & AOT_RELOC_JMP_TARGET_CODE)) {
          cur_ip = (unsigned)(code + aot_reloc_records[i].offset + 4);
        } else {
          cur_ip = 0;
        }

        if ((aot_reloc_records[i].relocation_type & AOT_RELOC_CODE_BLOCK)) {
          val = (unsigned)interp_action_to_code_block
            (aot_reloc_records[i].relocation_data);
        } else if ((aot_reloc_records[i].relocation_type & AOT_RELOC_RETURN_ADDRESS)) {
          val = (unsigned)(code + aot_reloc_records[i].offset + 4 + 3);
        } else {
          val = jit_frontend_aot_reloc_value
            (method, aot_reloc_records[i].relocation_data);
        }

        jit_assert (val - cur_ip
                    == *(uint32 *)(code + aot_reloc_records[i].offset));
        break;
      }
  }
  return true;
}

int
jit_codegen_x86_interp_jited_glue (void *self, JitInterpSwitchInfo *info,
                                   void *target)
{
  typedef int32 (*F)(const void *self, void *info, const void *target);
  union {F f; void *v;} u;
#ifdef CODEGEN_DUMP_LOWER_RESULT
  {
    void* method = jit_frontend_get_method_of_frame (info->frame);
    if (method != NULL) {
      LOG_VERBOSE("\nJITed Code of method : \t");
      jit_frontend_print_method_name (method);
    }
  }
  LOG_VERBOSE("\nJited Addr: 0x%x \n", (unsigned)target);
#endif
#if BEIHAI_ENABLE_JIT_LLVM == 0
  u.v = code_block_switch_to_jited_from_interp;
#else
  u.v = target;
#endif
  return u.f (self, info, target);
}

#ifndef CODEGEN_CHECK_ARGS

#define CHECK_EQKIND(reg0, reg1) (void)0
#define CHECK_CONST(reg0) (void)0
#define CHECK_NCONST(reg0) (void)0
#define CHECK_KIND(reg0, type) (void)0

#else

/* Check if two register's kind is equal */
#define CHECK_EQKIND(reg0, reg1)                    \
  do {                                              \
    if (jit_reg_kind (reg0) != jit_reg_kind (reg1)) \
      {                                             \
        PRINT_LINE;                                 \
        LOG_VERBOSE ("reg type not equal:\n");      \
        jit_dump_reg (cc, reg0);                    \
        jit_dump_reg (cc, reg1);                    \
        GOTO_FAIL;                                  \
      }                                             \
  } while (0)

/* Check if a register is an const */
#define CHECK_CONST(reg0)                           \
  do {                                              \
    if (!jit_reg_is_const (reg0))                   \
      {                                             \
        PRINT_LINE;                                 \
        LOG_VERBOSE ("reg is not const:\n");        \
        jit_dump_reg (cc, reg0);                    \
        GOTO_FAIL;                                  \
      }                                             \
  } while (0)

/* Check if a register is not an const */
#define CHECK_NCONST(reg0)                          \
  do {                                              \
    if (jit_reg_is_const (reg0))                    \
      {                                             \
        PRINT_LINE;                                 \
        LOG_VERBOSE ("reg is const:\n");            \
        jit_dump_reg (cc, reg0);                    \
        GOTO_FAIL;                                  \
      }                                             \
  } while (0)

/* Check if a register is a special type */
#define CHECK_KIND(reg0, type)                               \
  do {                                                       \
    if (jit_reg_kind (reg0) != type)                         \
      {                                                      \
        PRINT_LINE;                                          \
        LOG_VERBOSE ("invalid reg type %d, expected is: %d", \
                    jit_reg_kind (reg0), type);              \
        jit_dump_reg (cc, reg0);                             \
        GOTO_FAIL;                                           \
      }                                                      \
  } while (0)

#endif

/* Load one operand from insn and check none */
#define LOAD_1ARG                               \
  r0 = *jit_insn_opnd (insn, 0);

/* Load two operands from insn and check if r0 is non-const */
#define LOAD_2ARGS                              \
  r0 = *jit_insn_opnd (insn, 0);                \
  r1 = *jit_insn_opnd (insn, 1);                \
  CHECK_NCONST (r0)

/* Load three operands from insn and check if r0 is non-const */
#define LOAD_3ARGS                              \
  r0 = *jit_insn_opnd (insn, 0);                \
  r1 = *jit_insn_opnd (insn, 1);                \
  r2 = *jit_insn_opnd (insn, 2);                \
  CHECK_NCONST (r0)

/* Load three operands from insn and check none */
#define LOAD_3ARGS_NO_ASSIGN                    \
  r0 = *jit_insn_opnd (insn, 0);                \
  r1 = *jit_insn_opnd (insn, 1);                \
  r2 = *jit_insn_opnd (insn, 2);

/* Load four operands from insn and check if r0 is non-const */
#define LOAD_4ARGS                              \
  r0 = *jit_insn_opnd (insn, 0);                \
  r1 = *jit_insn_opnd (insn, 1);                \
  r2 = *jit_insn_opnd (insn, 2);                \
  r3 = *jit_insn_opnd (insn, 3);                \
  CHECK_NCONST (r0)

/**
 * Encode extending register of byte to register of dword
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src tho no of src register
 * @param is_signed the data is signed or unsigned
 *
 * @return return the next address of native code after encoded
 */
static char *
extend_r8_to_r32 (char *stream, int32 reg_no_dst,
                  int32 reg_no_src, bool is_signed)
{
  /* Should have been optimized by previous lower */
  if (is_signed)
    movsx_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src], SZ8);
  else
    movzx_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src], SZ8);

  return stream;
}

/**
 * Encode extending register of word to register of dword
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src tho no of src register
 * @param is_signed the data is signed or unsigned
 *
 * @return return the next address of native code after encoded
 */
static char *
extend_r16_to_r32 (char *stream, int32 reg_no_dst,
                   int32 reg_no_src, bool is_signed)
{
  if (is_signed)
    movsx_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src], SZ16);
  else
    movzx_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src], SZ16);

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT

#define fmov_r_m(i, m) do {     \
    fld_m (m);                  \
    fstp_r (i + 1);             \
  } while (0)

#define dmov_r_m(i, m) do {     \
    dld_m (m);                  \
    dstp_r (i + 1);             \
  } while (0)

#define fmov_m_r(m, i) do {     \
    if (i == 0)                 \
      fst_m (m);                \
    else {                      \
      fld_r (i);                \
      fstp_m (m);               \
    }                           \
  } while (0)

#define dmov_m_r(m, i) do {     \
    if (i == 0)                 \
      dst_m (m);                \
    else {                      \
      dld_r (i);                \
      dstp_m (m);               \
    }                           \
  } while (0)

#define fmov_mi_r(m, i) do {    \
    if (i == 0)                 \
      fist_m (m);               \
    else {                      \
      fld_r (i);                \
      fistp_m (m);              \
    }                           \
  } while (0)

#define dmov_mi_r(m, i) do {    \
    if (i == 0)                 \
      dist_m (m);               \
    else {                      \
      dld_r (i);                \
      distp_m (m);              \
    }                           \
  } while (0)

#define fmov_r_r(i0, i1) do {   \
    if (i0 != i1) {             \
      if (i1 == 0)              \
        fst_r (i0);             \
      else {                    \
        fld_r (i1);             \
        fstp_r (i0 + 1);        \
      }                         \
    }                           \
  } while (0)

#define dmov_r_r(i0, i1) do {   \
    if (i0 != i1) {             \
      if (i1 == 0)              \
        dst_r (i0);             \
      else {                    \
        dld_r (i1);             \
        dstp_r (i0 + 1);        \
      }                         \
    }                           \
  } while (0)

#define fmov_r_mi(i, m) do {    \
    fild_m (m);                 \
    fstp_r (i + 1);             \
  } while (0)

#define dmov_r_mi(i, m) do {    \
    dild_m (m);                 \
    dstp_r (i + 1);             \
  } while (0)

#define fmov_ri_m(r, m) do {    \
    fld_m (m);                  \
    fistp_m (m);                \
    mov_r_m (r, m);             \
  } while (0)

#define dmov_ri_m(r, m) do {    \
    dld_m (m);                  \
    fistp_m (m);                \
    mov_r_m (r, m);             \
  } while (0)

#define fmov_ri_r(r, i) do {    \
    M_Opnd _m;                  \
    m_from_jit_cache (_m);      \
    if (i == 0)                 \
      fist_m (_m);              \
    else {                      \
      fld_r (i);                \
      fistp_m (_m);             \
    }                           \
    mov_r_m (r, _m);            \
  } while (0)

#define dmov_ri_r(r, i) do {    \
    M_Opnd _m;                  \
    m_from_jit_cache (_m);      \
    if (i == 0)                 \
      fist_m (_m);              \
    else {                      \
      fld_r (i);                \
      fistp_m (_m);             \
    }                           \
    mov_r_m (r, _m);            \
  } while (0)

#define fmov_r_ri(i, r) do {    \
    M_Opnd _m;                  \
    m_from_jit_cache (_m);      \
    mov_m_r (_m, r);            \
    fmov_r_mi (i, _m);          \
  } while (0)

#define fdalu_r0_r(fd, op, i) do {          \
    if (op == ADD)                          \
      fd##add_r0_r (i);                     \
    else if (op == SUB)                     \
      fd##sub_r0_r (i);                     \
    else if (op == MUL)                     \
      fd##mul_r0_r (i);                     \
    else                                    \
      fd##div_r0_r (i);                     \
  } while (0)

#define fdalu_r(fd, op, i) do {             \
    if (op == ADD)                          \
      fd##add_r (i);                        \
    else if (op == SUB)                     \
      fd##sub_r (i);                        \
    else if (op == MUL)                     \
      fd##mul_r (i);                        \
    else                                    \
      fd##div_r (i);                        \
  } while (0)

#define fdalup_r(fd, op, i) do {            \
    if (op == ADD)                          \
      fd##addp_r (i);                       \
    else if (op == SUB)                     \
      fd##subp_r (i);                       \
    else if (op == MUL)                     \
      fd##mulp_r (i);                       \
    else                                    \
      fd##divp_r (i);                       \
  } while (0)

#define fdalu_m(fd, op, m) do {             \
    if (op == ADD)                          \
      fd##add_m (m);                        \
    else if (op == SUB)                     \
      fd##sub_m (m);                        \
    else if (op == MUL)                     \
      fd##mul_m (m);                        \
    else                                    \
      fd##div_m (m);                        \
  } while (0)

#define fdalu_r_r_imm(fd, kind, op, i0, i1, data) do {  \
    switch (op) {                                       \
      case ADD:                                         \
      case SUB:                                         \
      case MUL:                                         \
      case DIV:                                         \
        if (i0 != i1 ||                                 \
            (i0 == i1 && i0 == 0)) {                    \
          M_Opnd m;                                     \
          m_from_jit_cache (m);                         \
          MOV_IMM_##kind##_TO_M_Opnd (m, data);         \
          if (i0 != 0)                                  \
            fd##ld_r (i1);                              \
          else                                          \
            fd##mov_r_r (i0, i1);                       \
          fdalu_m (fd, op, m);                          \
          if (i0 != 0)                                  \
            fd##stp_r (i0 + 1);                         \
        }                                               \
        else {                                          \
          if (data == 0.0f || data == -0.0f)            \
            fld_zero ();                                \
          else if (data == 1.0f)                        \
            fld_one ();                                 \
          else {                                        \
            M_Opnd m;                                   \
            m_from_jit_cache (m);                       \
            MOV_IMM_##kind##_TO_M_Opnd (m, data);       \
            fd##ld_m (m);                               \
          }                                             \
          fdalup_r (fd, op, i0 + 1);                    \
        }                                               \
        break;                                          \
      case REM: /* already use call native */           \
      default:                                          \
        jit_assert (0);                                 \
        break;                                          \
    }                                                   \
  } while (0)

#define fdalu_r_imm_r(fd, kind, op, i0, data, i1) do {  \
    switch (op) {                                       \
      case ADD:                                         \
      case MUL:                                         \
        fdalu_r_r_imm(fd, kind, op, i0, i1, data);      \
        break;                                          \
      case SUB:                                         \
      case DIV: {                                       \
        if (data == 0.0f || data == -0.0f)              \
          fld_zero ();                                  \
        else if (data == 1.0f)                          \
          fld_one();                                    \
        else {                                          \
          M_Opnd m;                                     \
          m_from_jit_cache (m);                         \
          MOV_IMM_##kind##_TO_M_Opnd (m, data);         \
          fd##ld_m (m);                                 \
        }                                               \
        fdalu_r0_r (fd, op, i1 + 1);                    \
        fd##stp_r (i0 + 1);                             \
        break;                                          \
      }                                                 \
      case REM: /* already use call native */           \
      default:                                          \
        jit_assert (0);                                 \
        break;                                          \
    }                                                   \
  } while (0)

#define fdalu_r_r_r(fd, op, i0, i1, i2) do {\
    switch (op) {                           \
      case ADD:                             \
      case SUB:                             \
      case MUL:                             \
      case DIV:                             \
      {                                     \
        if (i0 == 0 && i2 != i0) {          \
          fd##mov_r_r (i0, i1);             \
          fdalu_r0_r (fd, op, i2);          \
        }                                   \
        else if (i2 == 0 && i0 == i1) {     \
          fdalu_r (fd, op, i0);             \
        }                                   \
        else if (i0 != 0 &&                 \
                 i1 == 0 && i2 == 0) {      \
          fd##st_r (i0);                    \
          fdalu_r0_r (fd, op, i2);          \
        }                                   \
        else if (i0 == i1) {                \
          fd##ld_r (i2);                    \
          fdalup_r (fd, op, i0 + 1);        \
        }                                   \
        else {                              \
          fd##ld_r (i1);                    \
          fdalu_r0_r (fd, op, i2 + 1);      \
          fd##stp_r (i0 + 1);               \
        }                                   \
        /* handle possible overflow */      \
        M_Opnd m;                           \
        m_from_jit_cache(m);                \
        if (i0 != 0) {                      \
          fd##ld_r(i0);                     \
        }                                   \
        fd##stp_m(m);                       \
        fd##ld_m(m);                        \
        if (i0 != 0) {                      \
          fd##stp_r(i0+1);                  \
        }                                   \
      }                                     \
        break;                              \
      case REM: /*already use call native */\
      default:                              \
        jit_assert (0);                     \
        break;                              \
    }                                       \
  } while (0)

#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode moving memory data expressed as M_Opnd to a register
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param is_signed the data is signed or unsigned
 * @param reg_no_dst the index of dest register
 * @param m the memory operand which contains the source data
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_M_Opnd_to_r (char *stream, uint32 bytes_dst, uint32 kind_dst,
                 bool is_signed, int32 reg_no_dst, M_Opnd m)
{
  if (kind_dst == JIT_REG_KIND_I4)
    {
      if (bytes_dst == 1)
        {
          if (is_signed)
            movsx_r_m (regs_I4[reg_no_dst], m, SZ8);
          else
            movzx_r_m (regs_I4[reg_no_dst], m, SZ8);
        }
      else if (bytes_dst == 2)
        {
          if (is_signed)
            movsx_r_m (regs_I4[reg_no_dst], m, SZ16);
          else
            movzx_r_m (regs_I4[reg_no_dst], m, SZ16);
        }
      else
        mov_r_m (regs_I4[reg_no_dst], m);
    }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
  else if (kind_dst == JIT_REG_KIND_F4)
    fmov_r_m (reg_no_dst, m);
  else if (kind_dst == JIT_REG_KIND_F8)
    dmov_r_m (reg_no_dst, m);
#endif

  return stream;
}

/**
 * Encode moving register data to memory which is expressed as M_Opnd
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param reg_no_src the index of source register
 * @param m the dest memory operand to store the data
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_r_to_M_Opnd (char *stream, uint32 bytes_dst, uint32 kind_dst,
                 int32 reg_no_src, M_Opnd m)
{
  if (kind_dst == JIT_REG_KIND_I4)
    {
      if (bytes_dst == 1)
        {
          /* Should have been optimized by previous lower */
          jit_assert (reg_no_src == REG_EAX_INDEX ||
                      reg_no_src == REG_EBX_INDEX ||
                      reg_no_src == REG_ECX_INDEX ||
                      reg_no_src == REG_EDX_INDEX);
          mov_m_r_with_size (m, regs_I4[reg_no_src], SZ8);
        }
      else if (bytes_dst == 2)
        mov_m_r_with_size (m, regs_I4[reg_no_src], SZ16);
      else
        mov_m_r (m, regs_I4[reg_no_src]);
    }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
  else if (kind_dst == JIT_REG_KIND_F4)
    fmov_m_r (m, reg_no_src);
  else if (kind_dst == JIT_REG_KIND_F8)
    dmov_m_r (m, reg_no_src);
#endif

  return stream;
}

/**
 * Encode loading register data from memory with imm base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param is_signed the data is signed or unsigned
 * @param reg_no_dst the index of dest register
 * @param base the base address of the memory
 * @param offset the offset address of the memory
 *
 * @return return the next address of native code after encoded
 */
static char *
ld_r_from_base_imm_offset_imm (char *stream, uint32 bytes_dst,
                               uint32 kind_dst, bool is_signed,
                               int32 reg_no_dst, int32 base,
                               int32 offset)
{
  M_Opnd m;

  m_from_d (m, base+offset);
  stream = mov_M_Opnd_to_r (stream, bytes_dst, kind_dst,
                            is_signed, reg_no_dst, m);

  return stream;
}

/**
 * Encode loading register data from memory with imm base and register offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param is_signed the data is signed or unsigned
 * @param reg_no_dst the index of dest register
 * @param base the base address of the memory
 * @param reg_no_offset the no of register which stores the offset of the memory
 *
 * @return return the next address of native code after encoded
 */
static char *
ld_r_from_base_imm_offset_r (char *stream, uint32 bytes_dst, uint32 kind_dst,
                             bool is_signed, int32 reg_no_dst,
                             int32 base, int32 reg_no_offset)
{
  M_Opnd m;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_offset]), base);
  stream = mov_M_Opnd_to_r (stream, bytes_dst, kind_dst,
                            is_signed, reg_no_dst, m);

  return stream;
}

/**
 * Encode loading register data from memory with register base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param is_signed the data is signed or unsigned
 * @param reg_no_dst the index of dest register
 * @param reg_no_base the no of register which stores the base of the memory
 * @param offset the offset address of the memory
 *
 * @return return the next address of native code after encoded
 */
static char *
ld_r_from_base_r_offset_imm (char *stream, uint32 bytes_dst, uint32 kind_dst,
                             bool is_signed, int32 reg_no_dst,
                             int32 reg_no_base, int32 offset)
{
  M_Opnd m;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_base]), offset);
  stream = mov_M_Opnd_to_r (stream, bytes_dst, kind_dst,
                            is_signed, reg_no_dst, m);

  return stream;
}

/**
 * Encode loading register data from memory with register base and register offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param is_signed the data is signed or unsigned
 * @param reg_no_dst the index of dest register
 * @param reg_no_base the no of register which stores the base of the memory
 * @param reg_no_offset the no of register which stores the offset of the memory
 *
 * @return return the next address of native code after encoded
 */
static char *
ld_r_from_base_r_offset_r (char *stream, uint32 bytes_dst, uint32 kind_dst,
                           bool is_signed, int32 reg_no_dst,
                           int32 reg_no_base, int32 reg_no_offset)
{
  M_Opnd m;

  m_from_d_b_i_s (m, 0, R_Opnd_get_reg_no(&regs_I4[reg_no_base]),
                  R_Opnd_get_reg_no(&regs_I4[reg_no_offset]), 0);
  stream = mov_M_Opnd_to_r (stream, bytes_dst, kind_dst,
                            is_signed, reg_no_dst, m);

  return stream;
}

/**
 * Encode storing register data to memory with imm base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param reg_no_src the index of src register
 * @param base the base address of the dst memory
 * @param offset the offset address of the dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_r_to_base_imm_offset_imm (char *stream, uint32 bytes_dst, uint32 kind_dst,
                             int32 reg_no_src, int32 base, int32 offset)
{
  M_Opnd m;

  m_from_d (m, base+offset);
  stream = mov_r_to_M_Opnd (stream, bytes_dst, kind_dst, reg_no_src, m);

  return stream;
}

/**
 * Encode storing register data to memory with imm base and register offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param reg_no_src the index of src register
 * @param base the base address of the dst memory
 * @param reg_no_offset the no of register which stores the offset of the dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_r_to_base_imm_offset_r (char *stream, uint32 bytes_dst, uint32 kind_dst,
                           int32 reg_no_src, int32 base,
                           int32 reg_no_offset)
{
  M_Opnd m;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_offset]), base);
  stream = mov_r_to_M_Opnd (stream, bytes_dst, kind_dst, reg_no_src, m);

  return stream;
}

/**
 * Encode storing register data to memory with register base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param reg_no_src the index of src register
 * @param reg_no_base the no of register which stores the base of the dst memory
 * @param offset the offset address of the dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_r_to_base_r_offset_imm (char *stream, uint32 bytes_dst, uint32 kind_dst,
                           int32 reg_no_src, int32 reg_no_base, int32 offset)
{
  M_Opnd m;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_base]), offset);
  stream = mov_r_to_M_Opnd (stream, bytes_dst, kind_dst, reg_no_src, m);

  return stream;
}

/**
 * Encode storing register data to memory with register base and register offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32), skipped by float/double
 * @param kind_dst the kind of data to move, could be I4, F4 or F8
 * @param reg_no_src the index of src register
 * @param reg_no_base the no of register which stores the base of the dst memory
 * @param reg_no_offset the no of register which stores the offset of the dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_r_to_base_r_offset_r (char *stream, uint32 bytes_dst, uint32 kind_dst,
                         int32 reg_no_src, int32 reg_no_base,
                         int32 reg_no_offset)
{
  M_Opnd m;

  m_from_d_b_i_s (m, 0, R_Opnd_get_reg_no(&regs_I4[reg_no_base]),
                  R_Opnd_get_reg_no(&regs_I4[reg_no_offset]), 0);
  stream = mov_r_to_M_Opnd (stream, bytes_dst, kind_dst, reg_no_src, m);

  return stream;
}

/**
 * Encode moving immediate data of Imm_Opnd to memory of M_Opnd
 *
 * @param m dst memory of M_Opnd type
 * @param imm src immediate data of Imm_Opnd type
 *
 * @return new stream
 */
static char *
mov_Imm_Opnd_to_M_Opnd (char *stream, M_Opnd m, Imm_Opnd imm,
                       int32 bytes_dst)
{
  if (bytes_dst == 1)
    mov_m_imm_with_size (m, imm, SZ8);
  else if (bytes_dst == 2)
    mov_m_imm_with_size (m, imm, SZ16);
  else
    mov_m_imm(m, imm);

  return stream;
}

/**
 * Encode storing int32 imm data to memory with imm base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32)
 * @param data_src the src immediate data
 * @param base the base address of dst memory
 * @param offset the offset address of dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_imm_to_base_imm_offset_imm (char *stream, uint32 bytes_dst,
                               void *data_src, int32 base, int32 offset)
{
  M_Opnd m;
  Imm_Opnd imm;
  uint32 bytes_dst1 = (bytes_dst <= 4) ? bytes_dst : 4;

  m_from_d (m, base + offset);
  imm_from_sz_v_s (imm, SZ32, *(int32*)data_src, true);
  stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, bytes_dst1);

  if (bytes_dst == 8)
    {
      m_from_d (m, base + offset + 4);
      imm_from_sz_v_s (imm, SZ32, *((int32*)data_src + 1), true);
      stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, 4);
    }

  return stream;
}

/**
 * Encode storing int32 imm data to memory with imm base and reg offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32)
 * @param data_src the src immediate data
 * @param base the base address of dst memory
 * @param reg_no_offset the no of register that stores the offset address
 *        of dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_imm_to_base_imm_offset_r (char *stream, uint32 bytes_dst, void *data_src,
                             int32 base, int32 reg_no_offset)
{
  M_Opnd m;
  Imm_Opnd imm;
  uint32 bytes_dst1 = (bytes_dst <= 4) ? bytes_dst : 4;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_offset]), base);
  imm_from_sz_v_s (imm, SZ32, *(int32*)data_src, true);
  stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, bytes_dst1);

  if (bytes_dst == 8)
    {
      m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_offset]), base + 4);
      imm_from_sz_v_s (imm, SZ32, *((int32*)data_src + 1), true);
      stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, 4);
    }

  return stream;
}

/**
 * Encode storing int32 imm data to memory with reg base and imm offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32)
 * @param data_src the src immediate data
 * @param reg_no_base the no of register that stores the base address
 *        of dst memory
 * @param offset the offset address of dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_imm_to_base_r_offset_imm (char *stream, uint32 bytes_dst, void *data_src,
                             int32 reg_no_base, int32 offset)
{
  M_Opnd m;
  Imm_Opnd imm;
  uint32 bytes_dst1 = (bytes_dst <= 4) ? bytes_dst : 4;

  m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_base]), offset);
  imm_from_sz_v_s (imm, SZ32, *(int32*)data_src, true);
  stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, bytes_dst1);

  if (bytes_dst == 8)
    {
      m_from_b_d (m, R_Opnd_get_reg_no (&regs_I4[reg_no_base]), offset + 4);
      imm_from_sz_v_s (imm, SZ32, *((int32*)data_src + 1), true);
      stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, 4);
    }

  return stream;
}

/**
 * Encode storing int32 imm data to memory with reg base and reg offset
 *
 * @param stream the address of native code to encode
 * @param bytes_dst the bytes number of the data,
 *        could be 1(byte), 2(short), 4(int32)
 * @param data_src the src immediate data
 * @param reg_no_base the no of register that stores the base address
 *        of dst memory
 * @param reg_no_offset the no of register that stores the offset address
 *        of dst memory
 *
 * @return return the next address of native code after encoded
 */
static char *
st_imm_to_base_r_offset_r (char *stream, uint32 bytes_dst, void *data_src,
                           int32 reg_no_base, int32 reg_no_offset)
{
  M_Opnd m;
  Imm_Opnd imm;
  uint32 bytes_dst1 = (bytes_dst <= 4) ? bytes_dst : 4;

  m_from_d_b_i_s (m, 0,
                  R_Opnd_get_reg_no (&regs_I4[reg_no_base]),
                  R_Opnd_get_reg_no (&regs_I4[reg_no_offset]),
                  0);
  imm_from_sz_v_s (imm, SZ32, *(int32*)data_src, true);
  stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, bytes_dst1);

  if (bytes_dst == 8)
    {
      m_from_d_b_i_s (m, 4,
                      R_Opnd_get_reg_no (&regs_I4[reg_no_base]),
                      R_Opnd_get_reg_no (&regs_I4[reg_no_offset]),
                      0);
      imm_from_sz_v_s (imm, SZ32, *((int32*)data_src + 1), true);
      stream = mov_Imm_Opnd_to_M_Opnd(stream, m, imm, 4);
    }

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT

/**
 * Encode moving immediate data of int32 to a memory operand
 *
 * @param m the memory operand
 * @param data the immediate data to mov, need to be 4 bytes
 */
#define MOV_IMM_I4_TO_M_Opnd(m, data) do {      \
    Imm_Opnd _imm;                              \
    imm_from_sz_v_s (_imm, SZ32, data, true);   \
    mov_m_imm (m, _imm);                        \
  } while (0)

/**
 * Encode moving immediate data of float to a memory operand
 *
 * @param m the memory operand
 * @param data the immediate data to mov, need to be 4 bytes
 */
#define MOV_IMM_F4_TO_M_Opnd(m, data) do {      \
    union_cache uc;                             \
    uc.f = data;                                \
    MOV_IMM_I4_TO_M_Opnd (m, uc.i);             \
  } while (0)

/**
 * Encode moving immediate data of double to a memory operand
 *
 * @param m the memory operand
 * @param data the immediate data to mov, need to be 8 bytes
 */
#define MOV_IMM_F8_TO_M_Opnd(m, data) do {      \
    M_Opnd m1;                                  \
    R_Opnd base = M_Opnd_get_base (&m);         \
    Imm_Opnd disp = M_Opnd_get_disp (&m);       \
    union_cache uc;                             \
    uc.d = data;                                \
    m_from_b_d (m1, R_Opnd_get_reg_no (&base),  \
                Imm_Opnd_get_value (&disp) + 4);\
    MOV_IMM_I4_TO_M_Opnd (m, uc.ui.i1);         \
    MOV_IMM_I4_TO_M_Opnd (m1, uc.ui.i2);        \
  } while (0)
    

static char *
fpu_cmp_imm_float_r (char *stream, float data, int i)
{
  float f1 = 0.0f, f2 = -0.0f, f3 = 1.0f;

  if (memcmp (&data, &f1, SZ_F4) == 0 ||
      memcmp (&data, &f2, SZ_F4) == 0)
    fld_zero ();
  else if (memcmp (&data, &f3, SZ_F4) == 0)
    fld_one ();
  else
    {
      M_Opnd m;

      m_from_jit_cache (m);
      MOV_IMM_F4_TO_M_Opnd (m, data);
      fld_m (m);
    }

  fcmpp_r (i + 1);

  return stream;
}

static char *
fpu_cmp_imm_double_r (char *stream, double data, int i)
{
  double f1 = 0.0f, f2 = -0.0f, f3 = 1.0f;

  if (memcmp (&data, &f1, SZ_F8) == 0 ||
      memcmp (&data, &f2, SZ_F8) == 0)
    fld_zero ();
  else if (memcmp (&data, &f3, SZ_F8) == 0)
    fld_one ();
  else
    {
      M_Opnd m;
      m_from_jit_cache (m);
      MOV_IMM_F8_TO_M_Opnd (m, data);
      dld_m (m);
    }

  fcmpp_r (i + 1);

  return stream;
}

static char *
fpu_cmp_r_m (char *stream, bool is_double, int i, M_Opnd m)
{
  if (i == 0)
    {
      if (is_double)
        dcmp_m (m);
      else
        fcmp_m (m);
    }
  else
    {
      fld_r (i);
      if (is_double)
        dcmpp_m (m);
      else
        fcmpp_m (m);
    }

  return stream;
}

static char *
fpu_cmp_r_r (char *stream, int i0, int i1)
{
  if (i0 == 0)
    fcmp_r (i1);
  else
    {
      fld_r (i0);
      fcmpp_r (i1 + 1);
    }

  return stream;
}

static char *
fpu_cmp_suffix (char *stream)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ8, 8, true);
  jpo (imm);
  alu_r_r (xor, reg_I4_free, reg_I4_free);
  imm_from_sz_v_s (imm, SZ32, 1, true);
  alu_r_imm (cmp, reg_I4_free, imm);

  return stream;
}

#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode moving immediate int32 data to register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst register
 * @param data the immediate data to move
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_imm_to_r_int32 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encode moving int32 data from src register to dst register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_r_to_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  if (reg_no_dst != reg_no_src)
    mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT
/**
 * Encode moving immediate float data to register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst register
 * @param data the immediate data to move
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_imm_to_r_float (char *stream, int32 reg_no, float data)
{
  float f1 = 0.0f, f2 = -0.0f, f3 = 1.0f;

  if (memcmp (&data, &f1, SZ_F4) == 0 ||
      memcmp (&data, &f2, SZ_F4) == 0)
    {
      fld_zero ();
      fstp_r (reg_no + 1);
    }
  else if (memcmp (&data, &f3, SZ_F4) == 0)
    {
      fld_one ();
      fstp_r (reg_no + 1);
    }
  else
    {
      M_Opnd m;

      m_from_jit_cache (m);
      MOV_IMM_F4_TO_M_Opnd (m, data);
      fmov_r_m (reg_no, m);
    }

  return stream;
}

/**
 * Encode moving float data from src register to dst register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_r_to_r_float (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  fmov_r_r (reg_no_dst, reg_no_src);

  return stream;
}

/**
 * Encode moving immediate double data to register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst register
 * @param data the immediate data to move
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_imm_to_r_double (char *stream, int32 reg_no, double data)
{
  double d1 = 0.0f, d2 = -0.0f, d3 = 1.0f;

  if (memcmp (&data, &d1, SZ_F8) == 0 ||
      memcmp (&data, &d2, SZ_F8) == 0)
    {
      fld_zero ();
      fstp_r (reg_no + 1);
    }
  else if (memcmp (&data, &d3, SZ_F8) == 0)
    {
      fld_one ();
      fstp_r (reg_no + 1);
    }
  else
    {
      M_Opnd m;

      m_from_jit_cache (m);
      MOV_IMM_F8_TO_M_Opnd (m, data);
      dmov_r_m (reg_no, m);
    }

  return stream;
}

/**
 * Encode moving double data from src register to dst register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register
 *
 * @return return the next address of native code after encoded
 */
static char *
mov_r_to_r_double (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  dmov_r_r (reg_no_dst, reg_no_src);

  return stream;
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encoding convert int32 immediate data to int8 register
 *
 * @param stream the address of native code to encode
 * @param reg_no the dst register, need to be converted to int8
 * @param data the src int32 immediate data
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_int8 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  if (data & 0x80)
    data |= 0xFFFFFF00;
  else
    data &= 0xFF;
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encoding convert int32 immediate data to int8 register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the dst register, need to be converted to int8
 * @param reg_no_src the src register
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_int8 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  return extend_r8_to_r32 (stream, reg_no_dst, reg_no_src, true);
}

/**
 * Encoding convert int32 immediate data to uint8 register
 *
 * @param stream the address of native code to encode
 * @param reg_no the dst register, need to be converted to uint8
 * @param data the src int32 immediate data
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_uint8 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  data &= 0xFF;
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encoding convert int32 immediate data to uint8 register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the dst register, need to be converted to uint8
 * @param reg_no_src the src register
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_uint8 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  return extend_r8_to_r32 (stream, reg_no_dst, reg_no_src, false);
}

/**
 * Encoding convert int32 immediate data to int16 register
 *
 * @param stream the address of native code to encode
 * @param reg_no the dst register, need to be converted to int16
 * @param data the src int32 immediate data
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_int16 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  if (data & 0x8000)
    data |= 0xFFFF0000;
  else
    data &= 0xFFFF;
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encoding convert int32 immediate data to int16 register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the dst register, need to be converted to int16
 * @param reg_no_src the src register
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_int16 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  return extend_r16_to_r32 (stream, reg_no_dst, reg_no_src, true);
}

/**
 * Encoding convert int32 immediate data to uint16 register
 *
 * @param stream the address of native code to encode
 * @param reg_no the dst register, need to be converted to uint16
 * @param data the src int32 immediate data
 *
 * @return  return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_uint16 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  data &= 0xFFFF;
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encoding convert int32 immediate data to uint16 register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the dst register, need to be converted to uint16
 * @param reg_no_src the src register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_uint16 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  return extend_r16_to_r32 (stream, reg_no_dst, reg_no_src, false);
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT

/**
 * Encode converting int32 immediate data to float register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst float register
 * @param data the src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_float (char *stream, int32 reg_no, int32 data)
{
  return mov_imm_to_r_float (stream, reg_no, (float)data);
}

/**
 * Encode converting int32 register data to float register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst float register
 * @param reg_no_src the no of src int32 register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_float (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  M_Opnd m;

  m_from_jit_cache (m);
  mov_m_r (m, regs_I4[reg_no_src]);
  fmov_r_mi (reg_no_dst, m);

  return stream;
}

/**
 * Encode converting int32 immediate data to double register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst double register
 * @param data the src immediate int32 data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_int32_to_r_double (char *stream, int32 reg_no, int32 data)
{
  return mov_imm_to_r_double (stream, reg_no, (double)data);
}

/**
 * Encode converting int32 register data to double register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst double register
 * @param reg_no_src the no of src int32 register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_int32_to_r_double (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  M_Opnd m;

  m_from_jit_cache (m);
  mov_m_r (m, regs_I4[reg_no_src]);
  fmov_r_mi (reg_no_dst, m);

  return stream;
}

/**
 * Encode converting float immediate data to int32 register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst int32 register
 * @param data the src immediate float data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_float_to_r_int32 (char *stream, int32 reg_no, float data)
{
  int32 val;

  if (data >= int32_max)
    val = int32_max;
  else if (data <= int32_min)
    val = int32_min;
  else if (data != data)
    val = 0;
  else
    val = (int32) data;

  return mov_imm_to_r_int32 (stream, reg_no, val);
}

/**
 * Encode converting float register data to int32 register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst int32 register
 * @param reg_no_src the no of src float register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_float_to_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  fmov_ri_r (regs_I4[reg_no_dst], reg_no_src);

  return stream;
}

/**
 * Encode converting float immediate data to double register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst double register
 * @param data the src immediate float data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_float_to_r_double (char *stream, int32 reg_no, float data)
{
  return mov_imm_to_r_double (stream, reg_no, (double)data);
}

/**
 * Encode converting float register data to double register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst double register
 * @param reg_no_src the no of src float register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_float_to_r_double (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  fmov_r_r (reg_no_dst, reg_no_src);

  return stream;
}

/**
 * Encode converting double immediate data to int32 register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst int32 register
 * @param data the src immediate double data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_double_to_r_int32 (char *stream, int32 reg_no, double data)
{
  int32 val;

  if (data >= int32_max)
    val = int32_max;
  else if (data <= int32_min)
    val = int32_min;
  else if (data != data)
    val = 0;
  else
    val = (int32) data;

  return mov_imm_to_r_int32 (stream, reg_no, val);
}

/**
 * Encode converting double register data to int32 register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst int32 register
 * @param reg_no_src the no of src double register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_double_to_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  dmov_ri_r (regs_I4[reg_no_dst], reg_no_src);

  return stream;
}

/**
 * Encode converting double immediate data to float register data
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst float register
 * @param data the src immediate double data
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_imm_double_to_r_float (char *stream, int32 reg_no, double data)
{
  return mov_imm_to_r_float (stream, reg_no, (float)data);
}

/**
 * Encode converting double register data to float register data
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst float register
 * @param reg_no_src the no of src double register
 *
 * @return return the next address of native code after encoded
 */
static char *
convert_r_double_to_r_float (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  dmov_r_r (reg_no_dst, reg_no_src);

  return stream;
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode making negative from int32 immediate data to int32 register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst register
 * @param data the src int32 immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_imm_to_r_int32 (char *stream, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, -data, true);
  mov_r_imm (regs_I4[reg_no], imm);

  return stream;
}

/**
 * Encode making negative from int32 register to int32 register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_r_to_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no_src)
{

  mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
  neg_r (regs_I4[reg_no_dst]);

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT
/**
 * Encode making negative from float immediate data to float register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst float register
 * @param data the src float immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_imm_to_r_float (char *stream, int32 reg_no, float data)
{
  return mov_imm_to_r_float (stream, reg_no, -data);
}

/**
 * Encode making negative from float register to float register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_r_to_r_float (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  if (reg_no_dst == 0)
    {
      fmov_r_r (reg_no_dst, reg_no_src);
      fneg ();
    }
  else
    {
      fld_r (reg_no_src);
      fneg ();
      fstp_r (reg_no_dst + 1);
    }

  return stream;
}

/**
 * Encode making negative from double immediate data to double register
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of dst double register
 * @param data the src double immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_imm_to_r_double (char *stream, int32 reg_no, double data)
{
  return mov_imm_to_r_double (stream, reg_no, -data);
}

/**
 * Encode making negative from double register to double register
 *
 * @param stream the address of native code to encode
 * @param reg_no_dst the no of dst double register
 * @param reg_no_src the no of src double register
 *
 * @return return the next address of native code after encoded
 */
static char *
neg_r_to_r_double (char *stream, int32 reg_no_dst, int32 reg_no_src)
{
  return neg_r_to_r_float (stream, reg_no_dst, reg_no_src);
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/* Alu opcode */
typedef enum { ADD, SUB, MUL, DIV, REM } ALU_OP;
/* Bit opcode */
typedef enum { OR, XOR, AND } BIT_OP;
/* Shift opcode */
typedef enum { SHL, SHRS, SHRU } SHIFT_OP;
/* Condition opcode */
typedef enum { EQ, NE, GTS, GES, LTS, LES, GTU, GEU, LTU, LEU } COND_OP;

static COND_OP
not_cond (COND_OP op)
{
  COND_OP not_list[] = { NE, EQ, LES, LTS, GES, GTS, LEU, LTU, GEU, GTU };

  jit_assert (op <= LEU);
  return not_list[op];
}

/**
 * Encode int32 alu operation of reg and data, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no the no of register, as first operand, and save result
 * @param data the immediate data, as the second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_r_imm_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
                   int32 reg_no_src, int32 data)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data, true);
  switch (op)
    {
      case ADD:
        mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        if (data == 1)
          inc_r (regs_I4[reg_no_dst]);
        else if (data == -1)
          dec_r (regs_I4[reg_no_dst]);
        else if (data != 0)
          alu_r_imm (add, regs_I4[reg_no_dst], imm);
        break;
      case SUB:
        mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        if (data == -1)
          inc_r (regs_I4[reg_no_dst]);
        else if (data == 1)
          dec_r (regs_I4[reg_no_dst]);
        else if (data != 0)
          alu_r_imm (sub, regs_I4[reg_no_dst], imm);
        break;
      case MUL:
        if (data == 0)
          alu_r_r (xor, regs_I4[reg_no_dst], regs_I4[reg_no_dst]);
        else if (data == -1)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
            neg_r (regs_I4[reg_no_dst]);
          }
        else if (data == 2)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
            imm_from_sz_v_s (imm, SZ8, 1, true);
            shift_r_imm (shl, regs_I4[reg_no_dst], imm);
          }
        else if (data == 4)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
            imm_from_sz_v_s (imm, SZ8, 2, true);
            shift_r_imm (shl, regs_I4[reg_no_dst], imm);
          }
        else if (data == 8)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
            imm_from_sz_v_s (imm, SZ8, 3, true);
            shift_r_imm (shl, regs_I4[reg_no_dst], imm);
          }
        else if (data != 1)
          imul_r_r_imm (regs_I4[reg_no_dst], regs_I4[reg_no_src], imm);
        else
          mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        break;
      case DIV:
      case REM:
        imm_from_sz_v_s (imm, SZ32, data, true);
        mov_r_imm (reg_I4_free, imm);
        stream = cdq (stream);
        idiv_r (reg_I4_free);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

static char *
div_r_r_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no1_src,
                 int32 reg_no2_src)
{
  stream = cdq (stream);
  idiv_r (regs_I4[reg_no2_src]);

  return stream;
}

static char *
neg_and_jmp (char *stream, int32 reg_no_dst, int32 reg_no_src, int32 len_jmp)
{
  Imm_Opnd imm;

  mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no_src]);
  neg_r (regs_I4[reg_no_dst]);
  imm_from_sz_v_s (imm, SZ8, len_jmp, true);
  jmp_imm (imm);

  return stream;
}

static char *
mov_divident_and_jmp (char *stream, int32 reg_no_dst,
                      int32 reg_no1_src, int32 len_jmp)
{
  Imm_Opnd imm;

  mov_r_r (regs_I4 [reg_no_dst], regs_I4[reg_no1_src]);
  imm_from_sz_v_s (imm, SZ8, len_jmp, true);
  jmp_imm (imm);

  return stream;
}

/**
 * Encode int32 alu operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register, as first operand, and save result
 * @param reg_no_src the no of register, as the second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_r_r_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
               int32 reg_no1_src, int32 reg_no2_src)
{
  Imm_Opnd imm;
  char stream_div[128], stream_neg[128], stream_mov[128];
  char *stream1 = stream_div;
  char *stream2 = stream_neg;
  char *stream3 = stream_mov;
  int32 len_div, len_neg, len_mov;

  stream1 = div_r_r_r_int32 (stream1, reg_no_dst, reg_no1_src, reg_no2_src);
  len_div = (int32)(stream1 - stream_div);
  stream2 = neg_and_jmp (stream2, reg_no_dst, reg_no1_src, len_div);
  len_neg = (int32)(stream2 - stream_neg);
  stream3 = mov_divident_and_jmp (stream3, reg_no_dst, reg_no1_src,
                                  len_neg + len_div + 0x8);
  len_mov = (int32)(stream3 - stream_mov);

  switch (op)
    {
      case ADD:
        if (reg_no_dst != reg_no2_src)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no1_src]);
            alu_r_r (add, regs_I4[reg_no_dst], regs_I4[reg_no2_src]);
          }
        else
          alu_r_r(add, regs_I4[reg_no2_src], regs_I4[reg_no1_src]);
        break;
      case SUB:
        if (reg_no_dst != reg_no2_src)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no1_src]);
            alu_r_r (sub, regs_I4[reg_no_dst], regs_I4[reg_no2_src]);
          }
        else
          {
            alu_r_r (sub, regs_I4[reg_no2_src], regs_I4[reg_no1_src]);
            neg_r (regs_I4[reg_no2_src]);
          }
        break;
      case MUL:
        if (reg_no_dst != reg_no2_src)
          {
            mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no1_src]);
            imul_r_r (regs_I4[reg_no_dst], regs_I4[reg_no2_src]);
          }
        else
            imul_r_r (regs_I4[reg_no2_src], regs_I4[reg_no1_src]);
        break;
      case DIV:
        /* if divisor is 1, the result is divdent */
        imm_from_sz_v_s (imm, SZ32, 1, true);
        alu_r_imm (cmp, regs_I4[reg_no2_src], imm);
        imm_from_sz_v_s (imm, SZ8, len_mov, true);
        jne (imm);

        memcpy (stream, stream_mov, len_mov);
        stream += len_mov;

        /* if divisor is -1, make negative */
        imm_from_sz_v_s (imm, SZ32, -1, true);
        alu_r_imm (cmp, regs_I4[reg_no2_src], imm);
        imm_from_sz_v_s (imm, SZ8, len_neg, true);
        jne (imm);

        memcpy (stream, stream_neg, len_neg);
        stream += len_neg;

        memcpy (stream, stream_div, len_div);
        stream += len_div;
        break;
      case REM:
        /* if divisor is 1, the result is 0 */
        imm_from_sz_v_s (imm, SZ32, 1, true);
        alu_r_imm (cmp, regs_I4[reg_no2_src], imm);
        imm_from_sz_v_s (imm, SZ8, 0xC, true);
        je (imm);

        /* if divisor is -1, the result is 0 */
        imm_from_sz_v_s (imm, SZ32, -1, true);
        alu_r_imm (cmp, regs_I4[reg_no2_src], imm);
        imm_from_sz_v_s (imm, SZ8, 4, true);
        jne (imm);

        alu_r_r (xor, regs_I4[reg_no_dst], regs_I4[reg_no_dst]);
        imm_from_sz_v_s (imm, SZ8, len_div, true);
        jmp_imm (imm);

        memcpy (stream, stream_div, len_div);
        stream += len_div;
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/**
 * Encode int32 alu operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_imm_to_r_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
                        int32 data1_src, int32 data2_src)
{
  Imm_Opnd imm;
  int32 data = 0;

  /* not div 0 or rem 0, calculate the result previously */
  switch (op)
    {
      case ADD:
        data = data1_src + data2_src;
        break;
      case SUB:
        data = data1_src - data2_src;
        break;
      case MUL:
        data = data1_src * data2_src;
        break;
      case DIV:
      case REM:
      default:
        jit_assert (0);
        break;
    }
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no_dst], imm);

  return stream;
}

/**
 * Encode int32 alu operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_r_to_r_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
                      int32 data1_src, int32 reg_no2_src)
{
  if (op == ADD || op == MUL)
    stream = alu_r_r_imm_int32 (stream, op, reg_no_dst,
                                reg_no2_src, data1_src);
  else if (op == SUB)
    {
      stream = alu_r_r_imm_int32 (stream, op, reg_no_dst,
                                  reg_no2_src, data1_src);
      neg_r (regs_I4[reg_no_dst]);
    }
  else
    {
      if (reg_no_dst != reg_no2_src)
        {
          stream = mov_imm_to_r_int32 (stream, reg_no_dst, data1_src);
          stream = alu_r_r_r_int32 (stream, op, reg_no_dst,
                                    reg_no_dst, reg_no2_src);
        }
      else
        {
          stream = mov_imm_to_r_int32 (stream, REG_I4_FREE_INDEX, data1_src);
          stream = alu_r_r_r_int32 (stream, op, reg_no_dst,
                                    REG_I4_FREE_INDEX, reg_no2_src);
        }
    }

  return stream;
}

/**
 * Encode int32 alu operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_imm_to_r_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
                        int32 reg_no1_src, int32 data2_src)
{
  stream = alu_r_r_imm_int32 (stream, op, reg_no_dst,
                              reg_no1_src, data2_src);

  return stream;
}

/**
 * Encode int32 alu operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_r_to_r_int32 (char *stream, ALU_OP op, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  stream = alu_r_r_r_int32 (stream, op, reg_no_dst,
                            reg_no1_src, reg_no2_src);

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT
/**
 * Encode float alu operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_imm_to_r_float (char *stream, ALU_OP op, int32 reg_no_dst,
                        float data1_src, float data2_src)
{
  float data;

  switch (op)
  {
    case ADD:
      data = data1_src + data2_src;
      break;
    case SUB:
      data = data1_src - data2_src;
      break;
    case MUL:
      data = data1_src * data2_src;
      break;
    case DIV:
      data = data1_src / data2_src;
      break;
    case REM:
      data = fmodf (data1_src, data2_src);
      break;
    default:
      jit_assert (0);
      break;
  }

  return mov_imm_to_r_float (stream, reg_no_dst, data);
}

/**
 * Encode float alu operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_r_to_r_float (char *stream, ALU_OP op, int32 reg_no_dst,
                      float data1_src, int32 reg_no2_src)
{
  if ((op == ADD || op == SUB) && (data1_src == 0.0f || data1_src == -0.0f))
    fmov_r_r (reg_no_dst, reg_no2_src);
  else if ((op == MUL || op == DIV) && data1_src == 1.0f)
    fmov_r_r (reg_no_dst, reg_no2_src);
  else if ((op == MUL || op == DIV) && data1_src == -1.0f)
    stream = neg_r_to_r_float (stream, reg_no_dst, reg_no2_src);
  else
    fdalu_r_imm_r (f, F4, op, reg_no_dst, data1_src, reg_no2_src);

  return stream;
}

/**
 * Encode float alu operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_imm_to_r_float (char *stream, ALU_OP op, int32 reg_no_dst,
                        int32 reg_no1_src, float data2_src)
{
  if ((op == ADD || op == SUB) && (data2_src == 0.0f || data2_src == -0.0f))
    fmov_r_r (reg_no_dst, reg_no1_src);
  else if ((op == MUL || op == DIV) && (data2_src == 1.0f))
    fmov_r_r (reg_no_dst, reg_no1_src);
  else if ((op == MUL || op == DIV) && (data2_src == -1.0f))
    stream = neg_r_to_r_float (stream, reg_no_dst, reg_no1_src);
  else
    fdalu_r_r_imm (f, F4, op, reg_no_dst, reg_no1_src, data2_src);

  return stream;
}

/**
 * Encode float alu operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_r_to_r_float (char *stream, ALU_OP op, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  fdalu_r_r_r (f, op, reg_no_dst, reg_no1_src, reg_no2_src);

  return stream;
}

/**
 * Encode double alu operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_imm_to_r_double (char *stream, ALU_OP op, int32 reg_no_dst,
                         double data1_src, double data2_src)
{
  double data;

  switch (op)
  {
    case ADD:
      data = data1_src + data2_src;
      break;
    case SUB:
      data = data1_src - data2_src;
      break;
    case MUL:
      data = data1_src * data2_src;
      break;
    case DIV:
      data = data1_src / data2_src;
      break;
    case REM:
      data = fmod (data1_src, data2_src);
      break;
    default:
      jit_assert (0);
      break;
  }

  return mov_imm_to_r_double (stream, reg_no_dst, data);
}

/**
 * Encode double alu operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_imm_r_to_r_double (char *stream, ALU_OP op, int32 reg_no_dst,
                       double data1_src, int32 reg_no2_src)
{
  if ((op == ADD || op == SUB) && (data1_src == 0.0f || data1_src == -0.0f))
    fmov_r_r (reg_no_dst, reg_no2_src);
  else if ((op == MUL || op == DIV) && data1_src == 1.0f)
    fmov_r_r (reg_no_dst, reg_no2_src);
  else if ((op == MUL || op == DIV) && data1_src == -1.0f)
    stream = neg_r_to_r_double (stream, reg_no_dst, reg_no2_src);
  else
    fdalu_r_imm_r (d, F8, op, reg_no_dst, data1_src, reg_no2_src);

  return stream;
}

/**
 * Encode double alu operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_imm_to_r_double (char *stream, ALU_OP op, int32 reg_no_dst,
                       int32 reg_no1_src, double data2_src)
{
  if ((op == ADD || op == SUB) && (data2_src == 0.0f || data2_src == -0.0f))
    fmov_r_r (reg_no_dst, reg_no1_src);
  else if ((op == MUL || op == DIV) && (data2_src == 1.0f))
    fmov_r_r (reg_no_dst, reg_no1_src);
  else if ((op == MUL || op == DIV) && (data2_src == -1.0f))
    stream = neg_r_to_r_double (stream, reg_no_dst, reg_no1_src);
  else
   fdalu_r_r_imm (d, F8, op, reg_no_dst, reg_no1_src, data2_src);

  return stream;
}

/**
 * Encode double alu operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of ALU operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
alu_r_r_to_r_double (char *stream, ALU_OP op, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  fdalu_r_r_r (d, op, reg_no_dst, reg_no1_src, reg_no2_src);

  return stream;
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode int32 bit operation of reg and data, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no the no of register, as first operand, and save result
 * @param data the immediate data, as the second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_r_imm_int32 (char *stream, BIT_OP op, int32 reg_no, int32 data)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data, true);
  switch (op)
    {
      case OR:
        alu_r_imm (or, regs_I4[reg_no], imm);
        break;
      case XOR:
        if (data == -1)
          not_r (regs_I4[reg_no]);
        else if (data != 0)
          alu_r_imm (xor, regs_I4[reg_no], imm);
        break;
      case AND:
        if (data != -1)
          alu_r_imm (and, regs_I4[reg_no], imm);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/**
 * Encode int32 bit operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no_dst the no of register, as first operand, and save result
 * @param reg_no_src the no of register, as second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_r_r_int32 (char *stream, BIT_OP op, int32 reg_no_dst, int32 reg_no_src)
{
  switch (op)
    {
      case OR:
        alu_r_r (or, regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        break;
      case XOR:
        alu_r_r (xor, regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        break;
      case AND:
        alu_r_r (and, regs_I4[reg_no_dst], regs_I4[reg_no_src]);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/**
 * Encode int32 bit operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_imm_imm_to_r_int32 (char *stream, BIT_OP op, int32 reg_no_dst,
    int32 data1_src, int32 data2_src)
{
  Imm_Opnd imm;
  int32 data = 0;

  switch (op)
    {
      case OR:
        data = data1_src | data2_src;
        break;
      case XOR:
        data = data1_src ^ data2_src;
        break;
      case AND:
        data = data1_src & data2_src;
        break;
      default:
        jit_assert (0);
        break;
    }
  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no_dst], imm);

  return stream;
}

/**
 * Encode int32 bit operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_imm_r_to_r_int32 (char *stream, BIT_OP op, int32 reg_no_dst,
    int32 data1_src, int32 reg_no2_src)
{
  if (op == AND && data1_src == 0)
    alu_r_r (xor, regs_I4[reg_no_dst], regs_I4[reg_no_dst]);
  else if (op == OR && data1_src == -1)
    {
      Imm_Opnd imm;

      imm_from_sz_v_s (imm, SZ32, -1, true);
      mov_r_imm (regs_I4[reg_no_dst], imm);
    }
  else
    {
      mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no2_src]);
      stream = bit_r_imm_int32 (stream, op, reg_no_dst, data1_src);
    }

  return stream;
}

/**
 * Encode int32 bit operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_r_imm_to_r_int32 (char *stream, BIT_OP op, int32 reg_no_dst,
    int32 reg_no1_src, int32 data2_src)
{
  return bit_imm_r_to_r_int32 (stream, op, reg_no_dst,
                               data2_src, reg_no1_src);
}

/**
 * Encode int32 bit operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of BIT operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
bit_r_r_to_r_int32 (char *stream, BIT_OP op, int32 reg_no_dst,
    int32 reg_no1_src, int32 reg_no2_src)
{
  if (reg_no_dst != reg_no2_src)
    {
      mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no1_src]);
      stream = bit_r_r_int32 (stream, op, reg_no_dst, reg_no2_src);
    }
  else
    stream = bit_r_r_int32 (stream, op, reg_no_dst, reg_no1_src);

  return stream;
}

/**
 * Encode int32 shift operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of SHIFT operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
shift_imm_imm_to_r_int32 (char *stream, SHIFT_OP op, int32 reg_no_dst,
    int32 data1_src, int32 data2_src)
{
  Imm_Opnd imm;
  int32 data = 0;

  switch (op)
    {
      case SHL:
        data = data1_src << data2_src;
        break;
      case SHRS:
        data = data1_src >> data2_src;
        break;
      case SHRU:
        data2_src %= 8 * SZ_I4;
        if (data2_src < 0)
          data2_src += 8 * SZ_I4;
        if (data2_src > 0)
          {
            data = data1_src >> data2_src;
            data &= ( 1 << (8 * SZ_I4 - data2_src) ) - 1;
          }
        else
          data = data1_src;
        break;
      default:
        jit_assert (0);
        break;
    }

  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (regs_I4[reg_no_dst], imm);

  return stream;
}

/**
 * Encode int32 shift operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of SHIFT operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
shift_imm_r_to_r_int32 (char *stream, SHIFT_OP op, int32 reg_no_dst,
                        int32 data1_src, int32 reg_no2_src)
{
  /* Should have been optimized by previous lower */
  jit_assert (0);

  return stream;
}

/**
 * Encode int32 shift operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of SHIFT operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
shift_r_imm_to_r_int32 (char *stream, SHIFT_OP op, int32 reg_no_dst,
                        int32 reg_no1_src, int32 data2_src)
{
  Imm_Opnd imm;

  mov_r_r (regs_I4[reg_no_dst], regs_I4[reg_no1_src]);

  imm_from_sz_v_s (imm, SZ8, data2_src, true);
  switch (op)
    {
      case SHL:
        shift_r_imm (shl, regs_I4[reg_no_dst], imm);
        break;
      case SHRS:
        shift_r_imm (sar, regs_I4[reg_no_dst], imm);
        break;
      case SHRU:
        shift_r_imm (shr, regs_I4[reg_no_dst], imm);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/**
 * Encode int32 shift operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of shift operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
shift_r_r_to_r_int32 (char *stream, SHIFT_OP op, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  switch (op)
    {
      case SHL:
        shift_r (shl, regs_I4[reg_no_dst]);
        break;
      case SHRS:
        shift_r (sar, regs_I4[reg_no_dst]);
        break;
      case SHRU:
        shift_r (shr, regs_I4[reg_no_dst]);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/**
 * Encode int32 cmp operation of reg and data, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of dst register
 * @param reg_no_src the no of src register, as first operand
 * @param data the immediate data, as the second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_imm_int32 (char *stream, int32 reg_no_dst, int32 reg_no_src, int32 data)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data, true);
  alu_r_imm (cmp, regs_I4[reg_no_src], imm);

  return stream;
}

/**
 * Encode int32 cmp operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of dst register
 * @param reg_no1_src the no of src register, as first operand
 * @param reg_no2_src the no of src register, as second operand
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_r_int32 (char *stream, int32 reg_no_dst, int32 reg_no1_src,
               int32 reg_no2_src)
{
  alu_r_r (cmp, regs_I4[reg_no1_src], regs_I4[reg_no2_src]);

  return stream;
}

/**
 * Encode int32 cmp operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_imm_to_r_int32 (char *stream, int32 reg_no_dst,
                        int32 data1_src, int32 data2_src)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data1_src, true);
  mov_r_imm (regs_I4[reg_no_dst], imm);
  imm_from_sz_v_s (imm, SZ32, data2_src, true);
  alu_r_imm (cmp, regs_I4[reg_no_dst], imm);

  return stream;
}

/**
 * Encode int32 cmp operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_r_to_r_int32 (char *stream, int32 reg_no_dst,
                      int32 data1_src, int32 reg_no2_src)
{
  Imm_Opnd imm;

  imm_from_sz_v_s (imm, SZ32, data1_src, true);
  mov_r_imm (reg_I4_free, imm);
  stream = cmp_r_r_int32 (stream, reg_no_dst, REG_I4_FREE_INDEX,
                          reg_no2_src);

  return stream;
}

/**
 * Encode int32 cmp operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_imm_to_r_int32 (char *stream, int32 reg_no_dst,
                      int32 reg_no1_src, int32 data2_src)
{
  stream = cmp_r_imm_int32 (stream, reg_no_dst, reg_no1_src, data2_src);

  return stream;
}

/**
 * Encode int32 cmp operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_r_to_r_int32 (char *stream, int32 reg_no_dst,
                    int32 reg_no1_src, int32 reg_no2_src)
{
  stream = cmp_r_r_int32 (stream, reg_no_dst, reg_no1_src, reg_no2_src);

  return stream;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT
/**
 * Encode float cmp operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_imm_to_r_float (char *stream, int32 reg_no_dst,
                        float data1_src, float data2_src)
{
  Imm_Opnd imm;
  int32 data = data1_src == data2_src ? 0 : (data1_src > data2_src ? 1 : -1);

  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (reg_I4_free, imm);
  imm_from_sz_v_s (imm, SZ32, 0, true);
  alu_r_imm (cmp, reg_I4_free, imm);
  return stream;
}

/**
 * Encode float cmp operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_r_to_r_float (char *stream, int32 reg_no_dst,
                      float data1_src, int32 reg_no2_src)
{
  uint32 float_NaN = 0x7FF80000;

  if (memcmp (&data1_src, &float_NaN, 4) == 0)
    {
      Imm_Opnd imm;

      /**
       * anything < NaN < NaN < anything, whenever the expression
       * has NaN, the result is always less than(<).
       */
      alu_r_r (xor, reg_I4_free, reg_I4_free);
      imm_from_sz_v_s (imm, SZ32, 1, true);
      alu_r_imm (cmp, reg_I4_free, imm);
      return stream;
    }

  stream = fpu_cmp_imm_float_r (stream, data1_src, reg_no2_src);
  return fpu_cmp_suffix (stream);
}

/**
 * Encode float cmp operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_imm_to_r_float (char *stream, int32 reg_no_dst,
                      int32 reg_no1_src, float data2_src)
{
  M_Opnd m;
  uint32 float_NaN = 0x7FF80000;

  if (memcmp (&data2_src, &float_NaN, 4) == 0)
    {
      Imm_Opnd imm;

      /**
       * anything < NaN < NaN < anything, whenever the expression
       * has NaN, the result is always less than(<).
       */
      alu_r_r (xor, reg_I4_free, reg_I4_free);
      imm_from_sz_v_s (imm, SZ32, 1, true);
      alu_r_imm (cmp, reg_I4_free, imm);
      return stream;
    }

  m_from_jit_cache (m);
  MOV_IMM_F4_TO_M_Opnd (m, data2_src);
  stream = fpu_cmp_r_m (stream, false, reg_no1_src, m);
  return fpu_cmp_suffix (stream);
}

/**
 * Encode float cmp operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_r_to_r_float (char *stream, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  stream = fpu_cmp_r_r (stream, reg_no1_src, reg_no2_src);
  return fpu_cmp_suffix (stream);
}

/**
 * Encode double cmp operation of imm and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_imm_to_r_double (char *stream, int32 reg_no_dst,
                         double data1_src, double data2_src)
{
  Imm_Opnd imm;
  int32 data = data1_src == data2_src ? 0 : (data1_src > data2_src ? 1 : -1);

  imm_from_sz_v_s (imm, SZ32, data, true);
  mov_r_imm (reg_I4_free, imm);
  imm_from_sz_v_s (imm, SZ32, 0, true);
  alu_r_imm (cmp, reg_I4_free, imm);
  return stream;
}

/**
 * Encode double cmp operation of imm and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param data1_src the first src immediate data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_imm_r_to_r_double (char *stream, int32 reg_no_dst,
                       double data1_src, int32 reg_no2_src)
{
  uint64 double_NaN = ((uint64)0x7FF80000) << 32;

  if (memcmp (&data1_src, &double_NaN, 8) == 0)
    {
      Imm_Opnd imm;

      /**
       * anything < NaN < NaN < anything, whenever the expression
       * has NaN, the result is always less than(<).
       */
      alu_r_r (xor, reg_I4_free, reg_I4_free);
      imm_from_sz_v_s (imm, SZ32, 1, true);
      alu_r_imm (cmp, reg_I4_free, imm);
      return stream;
    }

  stream = fpu_cmp_imm_double_r (stream, data1_src, reg_no2_src);
  return fpu_cmp_suffix (stream);
}

/**
 * Encode double cmp operation of reg and imm, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param data2_src the second src immediate data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_imm_to_r_double (char *stream, int32 reg_no_dst,
                        int32 reg_no1_src, double data2_src)
{
  M_Opnd m;
  uint64 double_NaN = ((uint64)0x7FF80000) << 32;

  if (memcmp (&data2_src, &double_NaN, 8) == 0)
    {
      Imm_Opnd imm;

      /**
       * anything < NaN < NaN < anything, whenever the expression
       * has NaN, the result is always less than(<).
       */
      alu_r_r (xor, reg_I4_free, reg_I4_free);
      imm_from_sz_v_s (imm, SZ32, 1, true);
      alu_r_imm (cmp, reg_I4_free, imm);
      return stream;
    }

  m_from_jit_cache (m);
  MOV_IMM_F8_TO_M_Opnd (m, data2_src);
  stream = fpu_cmp_r_m (stream, true, reg_no1_src, m);
  return fpu_cmp_suffix (stream);
}

/**
 * Encode double cmp operation of reg and reg, and save result to reg
 *
 * @param stream the address of native code to encode
 * @param op the opcode of cmp operation
 * @param reg_no_dst the no of register
 * @param reg_no1_src the reg no of first src register data
 * @param reg_no2_src the reg no of second src register data
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_r_to_r_double (char *stream, int32 reg_no_dst,
                      int32 reg_no1_src, int32 reg_no2_src)
{
  stream = fpu_cmp_r_r (stream, reg_no1_src, reg_no2_src);
  return fpu_cmp_suffix (stream);
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode detecting the cmp flags in reg, and jmp to the relative address
 * according to the condition opcode
 *
 * @param stream the address of native code to encode
 * @param reg_no the no of register which contains cmp flags of cmp result
 * @param op the condition opcode to jmp
 * @param offset the relative offset to jmp when the contidtion meeted
 *
 * @return return the next address of native code after encoded
 */
static char *
cmp_r_and_jmp_relative (char *stream, int32 reg_no, COND_OP op,
                        int32 offset)
{
  Imm_Opnd target;

  if (offset >= -127 && offset <= 127)
    imm_from_sz_v_s (target, SZ8, offset, true);
  else
    imm_from_sz_v_s (target, SZ32, offset, true);
  switch (op)
    {
      case EQ:
        je (target);
        break;
      case NE:
        jne (target);
        break;
      case GTS:
        jg (target);
        break;
      case LES:
        jng (target);
        break;
      case GES:
        jge (target);
        break;
      case LTS:
        jl (target);
        break;
      case GTU:
        ja (target);
        break;
      case LEU:
        jna (target);
        break;
      case GEU:
        jae (target);
        break;
      case LTU:
        jb (target);
        break;
      default:
        jit_assert (0);
        break;
    }

  return stream;
}

/* Jmp type */
typedef enum JmpType {
  JMP_DST_LABEL,        /* jmp to dst label */
  JMP_END_OF_CALLBC,    /* jmp to end of CALLBC */
  JMP_TABLE_SWITCH,     /* jmp to an entry of table_switch */
  JMP_TARGET_CODE       /* jmp to an function address */
} JmpType;

/**
 * Jmp info, save the info on first encoding pass,
 * and replace the offset with exact offset when the code cache
 * has been allocated actually.
 */
typedef struct JmpInfo {
  bh_list_link link;
  JmpType type;
  int32 label_src;
  int32 offset;
  union {
      int32 label_dst;
      int32 target_code_addr;
  } dst_info;
} JmpInfo;

static JmpInfo jmp_info_head;
static bh_list* jmp_info_list = (bh_list*) &jmp_info_head;

/* Pre-saved stream info when code cache has been allocated */
typedef struct StreamInfo {
  char *stream;
  int32 size;
} StreamInfo;

static StreamInfo *stream_list = NULL;

static bool
label_is_neighboring(JitCompContext *cc, int32 label_prev,
                     int32 label_succ)
{
  return (label_prev == 0 && label_succ == 2) ||
         (label_prev >= 2 && label_succ == label_prev + 1) ||
         (label_prev == (int32)jit_cc_label_num (cc) - 1 && label_succ == 1);
}

static bool
label_is_ahead(JitCompContext *cc, int32 label_dst, int32 label_src)
{
  return (label_dst == 0 && label_src != 0) ||
         (label_dst != 1 && label_src == 1) ||
         (2 <= label_dst && label_dst < label_src &&
          label_src <= (int32)jit_cc_label_num (cc) - 1);
}

static int32
label_get_offset(JitCompContext *cc, int32 label_dst, int32 label_src,
                 int32 stream_offset)
{
  int32 offset, label;

  jit_assert (label_is_ahead (cc, label_dst, label_src));

  offset = 0;
  if (label_src == 1)
    label_src = jit_cc_label_num (cc);

  for (label = label_dst; label < label_src && label != 1; label ++)
    offset += stream_list[label].size;

  offset += stream_offset;

  return -offset;
}

/**
 * Encode jumping from one label to the other label
 *
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_dst the index of dst label
 * @param label_src the index of src label
 *
 * @return true if success, false if failed
 */
static bool
jmp_from_label_to_label (char **stream_ptr, uint32 stream_offset,
                         int32 label_dst, int32 label_src)
{
  Imm_Opnd imm;
  JmpInfo *node;
  char *stream;

  stream = *stream_ptr;

  node = jit_malloc (sizeof (JmpInfo));
  if (!node)
    GOTO_FAIL;

  node->type = JMP_DST_LABEL;
  node->label_src = label_src;
  node->dst_info.label_dst = label_dst;
  node->offset = stream + 1 - (*stream_ptr - stream_offset);
  bh_list_insert (jmp_info_list, node);

  imm_from_sz_v_s (imm, SZ32, label_dst, true);
  jmp_imm (imm);

  *stream_ptr = stream;;
  return true;

fail:

  return false;
}

/**
 * Encode detecting compare result register according to condition code
 * and then jumping to suitable label when the condtion is meeted
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param op the opcode of condition operation
 * @param reg_no the no of register which contains the compare results
 * @param r1 the label info when condition meeted
 * @param r2 the label info when condition unmeeted, do nonthing if VOID
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
cmp_r_and_jmp_label (JitCompContext *cc, char **stream_ptr,
                     uint32 stream_offset, int32 label_src,
                     COND_OP op, int32 reg_no, JitReg r1, JitReg r2,
                     bool is_last_insn)
{
  Imm_Opnd imm;
  JmpInfo *node;
  char *stream;

  stream = *stream_ptr;

  node = jit_malloc (sizeof (JmpInfo));
  if (!node)
    GOTO_FAIL;

  node->type = JMP_DST_LABEL;
  node->label_src = label_src;
  node->dst_info.label_dst = jit_reg_no (r1);
  node->offset = stream + 2 - (*stream_ptr - stream_offset);
  bh_list_insert (jmp_info_list, node);

  imm_from_sz_v_s (imm, SZ32, jit_reg_no (r1), true);
  switch (op)
    {
      case EQ:
        je (imm);
        break;
      case NE:
        jne (imm);
        break;
      case GTS:
        jg (imm);
        break;
      case LES:
        jng (imm);
        break;
      case GES:
        jnl (imm);
        break;
      case LTS:
        jl (imm);
        break;
      case GTU:
        ja (imm);
        break;
      case LEU:
        jna (imm);
        break;
      case GEU:
        jnb (imm);
        break;
      case LTU:
        jb (imm);
        break;
      default:
        jit_assert (0);
        break;
    }

  if (r2)
    {
      int32 label_dst = jit_reg_no (r2);
      stream_offset += stream - *stream_ptr;
      if ( !(is_last_insn && label_is_neighboring (cc, label_src, label_dst)) )
        if (!jmp_from_label_to_label (&stream, stream_offset, label_dst, label_src))
          GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode insn ld: LD_type r0, r1, r2
 * @param kind the data kind, such as I4, F4 and F8
 * @param bytes_dst the byte number of dst data
 * @param is_signed the data is signed or unsigned
 */
#define LD_R_R_R(kind, bytes_dst, is_signed)                        \
  do {                                                              \
    int32 reg_no_dst;                                               \
    int32 base, offset;                                             \
                                                                    \
    CHECK_KIND (r1, JIT_REG_KIND_I4);                               \
    CHECK_KIND (r2, JIT_REG_KIND_I4);                               \
    base = 0;                                                       \
    offset = 0;                                                     \
    real_opnd_to_reg[1] = r2;                                       \
                                                                    \
    reg_no_dst = jit_reg_no (r0);                                   \
    if (jit_reg_is_const (r1))                                      \
      base = jit_cc_get_const_I4 (cc, r1);                          \
    if (jit_reg_is_const (r2))                                      \
      offset = jit_cc_get_const_I4 (cc, r2);                        \
                                                                    \
    if (jit_reg_is_const (r1))                                      \
      if (jit_reg_is_const (r2))                                    \
        stream = ld_r_from_base_imm_offset_imm (stream, bytes_dst,  \
                        JIT_REG_KIND_##kind, is_signed, reg_no_dst, \
                        base, offset);                              \
      else                                                          \
        stream = ld_r_from_base_imm_offset_r (stream, bytes_dst,    \
                        JIT_REG_KIND_##kind, is_signed, reg_no_dst, \
                        base, jit_reg_no (r2));                     \
    else                                                            \
      if (jit_reg_is_const (r2))                                    \
        stream = ld_r_from_base_r_offset_imm (stream, bytes_dst,    \
                        JIT_REG_KIND_##kind, is_signed, reg_no_dst, \
                        jit_reg_no (r1), offset);                   \
      else                                                          \
        stream = ld_r_from_base_r_offset_r (stream, bytes_dst,      \
                        JIT_REG_KIND_##kind, is_signed, reg_no_dst, \
                        jit_reg_no (r1), jit_reg_no (r2));          \
  } while (0)

/**
 * Encode insn sd: ST_type r0, r1, r2
 * @param kind the data kind, such as I4, F4 and F8
 * @param bytes_dst the byte number of dst data
 */
#define ST_R_R_R(kind, type, bytes_dst)                             \
  do {                                                              \
    type data_src = 0;                                              \
    int32 reg_no_src = 0;                                           \
    int32 base, offset;                                             \
                                                                    \
    CHECK_KIND (r1, JIT_REG_KIND_I4);                               \
    CHECK_KIND (r2, JIT_REG_KIND_I4);                               \
    base = 0;                                                       \
    offset = 0;                                                     \
    real_opnd_to_reg[0] = r2;                                       \
    real_opnd_to_reg[1] = r0;                                       \
                                                                    \
    if (jit_reg_is_const (r0))                                      \
      data_src = jit_cc_get_const_##kind (cc, r0);                  \
    else                                                            \
      reg_no_src = jit_reg_no (r0);                                 \
    if (jit_reg_is_const (r1))                                      \
      base = jit_cc_get_const_I4 (cc, r1);                          \
    if (jit_reg_is_const (r2))                                      \
      offset = jit_cc_get_const_I4 (cc, r2);                        \
                                                                    \
    if (jit_reg_is_const (r0))                                      \
      if (jit_reg_is_const (r1))                                    \
        if (jit_reg_is_const (r2))                                  \
          stream = st_imm_to_base_imm_offset_imm (stream, bytes_dst,\
                            &data_src,                              \
                            base, offset);                          \
        else                                                        \
          stream = st_imm_to_base_imm_offset_r (stream, bytes_dst,  \
                            &data_src,                              \
                            base, jit_reg_no (r2));                 \
      else                                                          \
        if (jit_reg_is_const (r2))                                  \
          stream = st_imm_to_base_r_offset_imm (stream, bytes_dst,  \
                            &data_src,                              \
                            jit_reg_no (r1), offset);               \
        else                                                        \
          stream = st_imm_to_base_r_offset_r (stream, bytes_dst,    \
                            &data_src,                              \
                            jit_reg_no (r1), jit_reg_no (r2));      \
    else                                                            \
      if (jit_reg_is_const (r1))                                    \
        if (jit_reg_is_const (r2))                                  \
          stream = st_r_to_base_imm_offset_imm (stream, bytes_dst,  \
                            JIT_REG_KIND_##kind, reg_no_src,        \
                            base, offset);                          \
        else                                                        \
          stream = st_r_to_base_imm_offset_r (stream, bytes_dst,    \
                            JIT_REG_KIND_##kind, reg_no_src,        \
                            base, jit_reg_no (r2));                 \
      else                                                          \
        if (jit_reg_is_const (r2))                                  \
          stream = st_r_to_base_r_offset_imm (stream, bytes_dst,    \
                            JIT_REG_KIND_##kind, reg_no_src,        \
                            jit_reg_no (r1), offset);               \
        else                                                        \
          stream = st_r_to_base_r_offset_r (stream, bytes_dst,      \
                            JIT_REG_KIND_##kind, reg_no_src,        \
                            jit_reg_no (r1), jit_reg_no (r2));      \
  } while (0)

/**
 * Encode insn mov: MOV r0, r1
 * @param kind the data kind, such as I4, F4 and F8
 * @param bytes_dst the byte number of dst data
 */
#define MOV_R_R(kind, type)                                             \
  do {                                                                  \
    CHECK_EQKIND (r0, r1);                                              \
    if (jit_reg_is_const (r1))                                          \
      {                                                                 \
        type data = jit_cc_get_const_##kind (cc, r1);                   \
        stream = mov_imm_to_r_##type (stream, jit_reg_no (r0), data);   \
      }                                                                 \
    else                                                                \
      stream = mov_r_to_r_##type (stream, jit_reg_no (r0),              \
                                          jit_reg_no (r1));             \
  } while (0)

/**
 * Encode mov insn, MOV r0, r1
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_mov (JitCompContext *cc, char **stream_ptr, JitReg r0, JitReg r1)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r0))
    {
      case JIT_REG_KIND_I4:
        MOV_R_R (I4, int32);
        BREAK;
#ifdef CODEGEN_ENABLE_FLOATING_POINT
      case JIT_REG_KIND_F4:
        MOV_R_R (F4, float);
        BREAK;
      case JIT_REG_KIND_F8:
        MOV_R_R (F8, double);
        BREAK;
#endif
      default:
        LOG_VERBOSE ("Invalid reg type of mov: %d\n",
                    jit_reg_kind (r0));
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

#ifdef BEIHAI_JIT_FOR_DALVIK
static bool
lower_checkgc (JitCompContext *cc, char **stream_ptr,
               uint32 stream_offset, int32 label_src)
{
  char *stream = *stream_ptr;
  M_Opnd m;
  Imm_Opnd imm;
  JmpInfo *node;
  extern unsigned dex_check_suspending;

  /* load self */
  m_from_b_d (m, esp_reg, 16 + 4);
  mov_r_m (reg_I4_free, m);
  /* load suspend count */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 48);
  /* cmp count, 0 */
  imm_from_sz_v_s (imm, SZ32, 0, true);
  alu_m_imm (cmp, m, imm);
  imm_from_sz_v_s (imm, SZ32, 25, true);
  je (imm);

  push_r (eax);
  push_r (ecx);
  push_r (edx);

  push_r (reg_I4_free);

  node = jit_malloc (sizeof (JmpInfo));
  if (!node)
    GOTO_FAIL;

  node->type = JMP_TARGET_CODE;
  node->label_src = label_src;
  node->offset = (int32) (stream + 1 - (*stream_ptr - stream_offset));
  node->dst_info.target_code_addr = (int32)dex_check_suspending;
  bh_list_insert (jmp_info_list, node);

  imm_from_sz_v_s (imm, SZ32, dex_check_suspending, true);
  call_imm (imm);
  imm_from_sz_v_s (imm, SZ32, 4, true);
  alu_r_imm (add, esp, imm);

  pop_r (edx);
  pop_r (ecx);
  pop_r (eax);

  *stream_ptr = stream;
  return true;

fail:
  return false;
}
#endif

/**
 * Encode insn neg: NEG r0, r1
 * @param kind the data kind, such as I4, F4 and F8
 * @param type the data type, such as int32, float and double
 */
#define NEG_R_R(kind, type)                                         \
  do {                                                              \
    CHECK_EQKIND (r0, r1);                                          \
    if (jit_reg_is_const (r1))                                      \
      {                                                             \
        type data = jit_cc_get_const_##kind (cc, r1);               \
        stream = neg_imm_to_r_##type (stream, jit_reg_no (r0),      \
                                      data);                        \
      }                                                             \
    else                                                            \
      stream = neg_r_to_r_##type (stream, jit_reg_no (r0),          \
                                  jit_reg_no (r1));                 \
  } while (0)

/**
 * Encode neg insn, NEG r0, r1
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_neg (JitCompContext *cc, char **stream_ptr, JitReg r0, JitReg r1)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r0))
    {
      case JIT_REG_KIND_I4:
        NEG_R_R (I4, int32);
        BREAK;
#ifdef CODEGEN_ENABLE_FLOATING_POINT
      case JIT_REG_KIND_F4:
        NEG_R_R (F4, float);
        BREAK;
      case JIT_REG_KIND_F8:
        NEG_R_R (F8, double);
        BREAK;
#endif
      default:
        LOG_VERBOSE ("Invalid reg type of neg: %d\n",
                    jit_reg_kind (r0));
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode insn convert: I4TOI1 r0, r1, or I4TOI2, I4TOF4, F4TOF8, etc.
 * @param kind0 the dst data kind, such as I4, F4 and F8
 * @param kind1 the src data kind, such as I4, F4 and F8
 * @param type0 the dst data type, such as int32, float and double
 * @param type1 the src data type, such as int32, float and double
 */
#define CONVERT_R_R(kind0, kind1, type0, type1)                     \
  do {                                                              \
    CHECK_KIND (r0, JIT_REG_KIND_##kind0);                          \
    CHECK_KIND (r1, JIT_REG_KIND_##kind1);                          \
    if (jit_reg_is_const (r1))                                      \
      {                                                             \
        type1 data = jit_cc_get_const_##kind1 (cc, r1);             \
        stream = convert_imm_##type1##_to_r_##type0 (stream,        \
                      jit_reg_no (r0), data);                       \
      }                                                             \
    else                                                            \
      stream = convert_r_##type1##_to_r_##type0 (stream,            \
                      jit_reg_no (r0), jit_reg_no (r1));            \
  } while (0)

/**
 * Encode insn alu: ADD/SUB/MUL/DIV/REM r0, r1, r2
 * @param kind the data kind, such as I4, F4 and F8
 * @param type the data type, such as int32, float and double
 * @param op the opcode of alu
 */
#define ALU_R_R_R(kind, type, op)                                   \
  do {                                                              \
    type data1, data2;                                              \
    int32 reg_no_dst;                                               \
                                                                    \
    CHECK_EQKIND (r0, r1);                                          \
    CHECK_EQKIND (r0, r2);                                          \
    memset (&data1, 0, sizeof(type));                               \
    memset (&data2, 0, sizeof(type));                               \
                                                                    \
    reg_no_dst = jit_reg_no (r0);                                   \
    if (jit_reg_is_const (r1))                                      \
      data1 = jit_cc_get_const_##kind (cc, r1);                     \
    if (jit_reg_is_const (r2))                                      \
      data2 = jit_cc_get_const_##kind (cc, r2);                     \
                                                                    \
    if (jit_reg_is_const (r1))                                      \
      if (jit_reg_is_const (r2))                                    \
        stream = alu_imm_imm_to_r_##type (stream, op, reg_no_dst,   \
                                        data1, data2);              \
      else                                                          \
        stream = alu_imm_r_to_r_##type (stream, op, reg_no_dst,     \
                                        data1, jit_reg_no (r2));    \
    else                                                            \
      if (jit_reg_is_const (r2))                                    \
        stream = alu_r_imm_to_r_##type (stream, op, reg_no_dst,     \
                                jit_reg_no (r1), data2);            \
      else                                                          \
        stream = alu_r_r_to_r_##type (stream, op, reg_no_dst,       \
                                jit_reg_no (r1), jit_reg_no(r2));   \
  } while (0)

/**
 * Encode alu insn, ADD/SUB/MUL/DIV/REM r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param op the opcode of alu operations
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_alu (JitCompContext *cc, char **stream_ptr, ALU_OP op,
               JitReg r0, JitReg r1, JitReg r2)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r0))
    {
      case JIT_REG_KIND_I4:
        ALU_R_R_R (I4, int32, op);
        BREAK;
#ifdef CODEGEN_ENABLE_FLOATING_POINT
      case JIT_REG_KIND_F4:
        ALU_R_R_R (F4, float, op);
        BREAK;
      case JIT_REG_KIND_F8:
        ALU_R_R_R (F8, double, op);
        BREAK;
#endif
      default:
        LOG_VERBOSE ("Invalid reg type of alu: %d\n",
                    jit_reg_kind (r0));
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode insn bit: AND/OR/XOR r0, r1, r2
 * @param kind the data kind, such as I4, F4 and F8
 * @param type the data type, such as int32, float and double
 * @param op the opcode of bit operation
 */
#define BIT_R_R_R(kind, type, op)                                   \
  do {                                                              \
    type data1, data2;                                              \
    int32 reg_no_dst;                                               \
                                                                    \
    CHECK_EQKIND (r0, r1);                                          \
    CHECK_EQKIND (r0, r2);                                          \
    memset (&data1, 0, sizeof(type));                               \
    memset (&data2, 0, sizeof(type));                               \
                                                                    \
    reg_no_dst = jit_reg_no (r0);                                   \
    if (jit_reg_is_const (r1))                                      \
        data1 = jit_cc_get_const_##kind (cc, r1);                   \
    if (jit_reg_is_const (r2))                                      \
        data2 = jit_cc_get_const_##kind (cc, r2);                   \
                                                                    \
    if (jit_reg_is_const (r1))                                      \
      if (jit_reg_is_const (r2))                                    \
        stream = bit_imm_imm_to_r_##type (stream, op, reg_no_dst,   \
                                        data1, data2);              \
      else                                                          \
        stream = bit_imm_r_to_r_##type (stream, op, reg_no_dst,     \
                                        data1, jit_reg_no (r2));    \
    else                                                            \
      if (jit_reg_is_const (r2))                                    \
        stream = bit_r_imm_to_r_##type (stream, op, reg_no_dst,     \
                                jit_reg_no (r1), data2);            \
      else                                                          \
        stream = bit_r_r_to_r_##type (stream, op, reg_no_dst,       \
                                jit_reg_no (r1), jit_reg_no(r2));   \
  } while (0)

/**
 * Encode bit insn, AND/OR/XOR r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param op the opcode of bit operations
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_bit (JitCompContext *cc, char **stream_ptr, BIT_OP op,
           JitReg r0, JitReg r1, JitReg r2)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r0))
    {
      case JIT_REG_KIND_I4:
        BIT_R_R_R (I4, int32, op);
        BREAK;
      default:
        LOG_VERBOSE ("Invalid reg type of bit: %d\n",
                    jit_reg_kind (r0));
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode insn shift: SHL/SHRS/SHRU r0, r1, r2
 * @param kind the data kind, should only be I4
 * @param type the data type, should only be int32
 * @param op the opcode of shift operation
 */
#define SHIFT_R_R_R(kind, type, op)                                 \
  do {                                                              \
    type data1, data2;                                              \
    int32 reg_no_dst;                                               \
                                                                    \
    CHECK_EQKIND (r0, r1);                                          \
    CHECK_KIND (r2, JIT_REG_KIND_I4);                               \
    memset (&data1, 0, sizeof(type));                               \
    memset (&data2, 0, sizeof(type));                               \
                                                                    \
    reg_no_dst = jit_reg_no (r0);                                   \
    if (jit_reg_is_const (r1))                                      \
        data1 = jit_cc_get_const_##kind (cc, r1);                   \
    if (jit_reg_is_const (r2))                                      \
        data2 = jit_cc_get_const_##kind (cc, r2);                   \
                                                                    \
    if (jit_reg_is_const (r1))                                      \
      if (jit_reg_is_const (r2))                                    \
        stream = shift_imm_imm_to_r_##type (stream, op, reg_no_dst, \
                                            data1, data2);          \
      else                                                          \
        stream = shift_imm_r_to_r_##type (stream, op, reg_no_dst,   \
                                          data1, jit_reg_no (r2));  \
    else                                                            \
      if (jit_reg_is_const (r2))                                    \
        stream = shift_r_imm_to_r_##type (stream, op, reg_no_dst,   \
                                          jit_reg_no (r1), data2);  \
      else                                                          \
        stream = shift_r_r_to_r_##type (stream, op, reg_no_dst,     \
                                        jit_reg_no (r1),            \
                                        jit_reg_no(r2));            \
  } while (0)

/**
 * Encode shift insn, SHL/SHRS/SHRU r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param op the opcode of shift operations
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_shift (JitCompContext *cc, char **stream_ptr, SHIFT_OP op,
             JitReg r0, JitReg r1, JitReg r2)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r0))
    {
      case JIT_REG_KIND_I4:
        SHIFT_R_R_R (I4, int32, op);
        BREAK;
      default:
        LOG_VERBOSE ("Invalid reg type of shift: %d\n",
                    jit_reg_kind (r0));
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode insn cmp: CMP r0, r1, r2
 * @param kind the data kind, such as I4, F4 and double
 * @param type the data type, such as int32, float and double
 */
#define CMP_R_R_R(kind, type)                                       \
  do {                                                              \
    type data1, data2;                                              \
    int32 reg_no_dst;                                               \
                                                                    \
    CHECK_KIND (r0, JIT_REG_KIND_I4);                               \
    CHECK_KIND (r1, JIT_REG_KIND_##kind);                           \
    CHECK_EQKIND (r1, r2);                                          \
    memset (&data1, 0, sizeof(type));                               \
    memset (&data2, 0, sizeof(type));                               \
                                                                    \
    reg_no_dst = jit_reg_no (r0);                                   \
    if (jit_reg_is_const (r1))                                      \
      data1 = jit_cc_get_const_##kind (cc, r1);                     \
    if (jit_reg_is_const (r2))                                      \
      data2 = jit_cc_get_const_##kind (cc, r2);                     \
                                                                    \
    if (jit_reg_is_const (r1))                                      \
      if (jit_reg_is_const (r2))                                    \
        stream = cmp_imm_imm_to_r_##type (stream, reg_no_dst,       \
                                          data1, data2);            \
      else                                                          \
        stream = cmp_imm_r_to_r_##type (stream, reg_no_dst,         \
                                        data1, jit_reg_no (r2));    \
    else                                                            \
      if (jit_reg_is_const (r2))                                    \
        stream = cmp_r_imm_to_r_##type (stream, reg_no_dst,         \
                                jit_reg_no (r1), data2);            \
      else                                                          \
        stream = cmp_r_r_to_r_##type (stream, reg_no_dst,           \
                                jit_reg_no (r1), jit_reg_no(r2));   \
  } while (0)

/**
 * Encode cmp insn, CMP r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_cmp (JitCompContext *cc, char **stream_ptr,
           JitReg r0, JitReg r1, JitReg r2)
{
  char *stream = *stream_ptr;

  switch (jit_reg_kind (r1))
   {
     case JIT_REG_KIND_I4:
       CMP_R_R_R (I4, int32);
       BREAK;
#ifdef CODEGEN_ENABLE_FLOATING_POINT
     case JIT_REG_KIND_F4:
       CMP_R_R_R (F4, float);
       BREAK;
     case JIT_REG_KIND_F8:
       CMP_R_R_R (F8, double);
       BREAK;
#endif
     default:
       LOG_VERBOSE ("Invalid reg type of cmp: %d\n",
                   jit_reg_kind (r1));
       GOTO_FAIL;
   }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

static bool
lower_xcmpl_int32 (JitCompContext *cc, char **stream_ptr,
                   JitReg r0, JitReg r1, JitReg r2, bool is_signed)
{
  char *stream = *stream_ptr;
  bool is_reversed = false;
  int32 data1 = 0, data2 = 0;
  R_Opnd reg0, reg1, reg2;
  Imm_Opnd imm;

  reg0 = regs_I4[jit_reg_no (r0)];

  if (jit_reg_is_const (r1))
    data1 = jit_cc_get_const_I4 (cc, r1);
  if (jit_reg_is_const (r2))
    data2 = jit_cc_get_const_I4 (cc, r2);

  if (jit_reg_is_const (r1) && jit_reg_is_const (r2))
    {
      int32 result = data1 == data2 ? 0 : (data1 > data2 ? 1 : -1);

      imm_from_sz_v_s (imm, SZ32, result, true);
      mov_r_imm (reg0, imm);
      *stream_ptr = stream;
      return true;
    }

  if (jit_reg_is_const (r1))
    {
      imm_from_sz_v_s (imm, SZ32, data1, true);
      reg2 = regs_I4[jit_reg_no (r2)];
      alu_r_imm (cmp, reg2, imm);
      is_reversed = true;
    }
  else if (jit_reg_is_const (r2))
    {
      reg1 = regs_I4[jit_reg_no (r1)];
      imm_from_sz_v_s (imm, SZ32, data2, true);
      alu_r_imm (cmp, reg1, imm);
    }
  else
    {
      reg1 = regs_I4[jit_reg_no (r1)];
      reg2 = regs_I4[jit_reg_no (r2)];
      alu_r_r (cmp, reg1, reg2);
    }

  imm_from_sz_v_s (imm, SZ32, 1, true);
  mov_r_imm (reg0, imm);

  imm_from_sz_v_s (imm, SZ8, 0xB, true);
  if (is_signed)
    {
      if (!is_reversed)
        jg (imm);
      else
        jl (imm);
    }
  else
    {
      if (!is_reversed)
        ja (imm);
      else
        jb (imm);
    }

  imm_from_sz_v_s (imm, SZ8, 7, true);
  jz (imm);

  imm_from_sz_v_s (imm, SZ32, -1, true);
  mov_r_imm (reg0, imm);
  imm_from_sz_v_s (imm, SZ8, 2, true);
  jmp_imm (imm);

  alu_r_r (xor, reg0, reg0);

  *stream_ptr = stream;
  return true;
}

#ifdef CODEGEN_ENABLE_FLOATING_POINT
static char *
fpu_lower_xcmpu_suffix (char *stream, JitReg r0, bool is_xcmpl)
{
  R_Opnd reg0;
  Imm_Opnd imm;

  reg0 = regs_I4[jit_reg_no (r0)];
  imm_from_sz_v_s (imm, SZ32, ((is_xcmpl) ? -1 : 1), true);
  mov_r_imm (reg0, imm);

  /**
   * need check CF flag first, since when comparing with NaN(whenever Nan
   * exists in left side or right side), the result will alawys be treated as
   * below(<) and will also set the CF flag.
   */
  imm_from_sz_v_s (imm, SZ8, 0xB, true);
  jb (imm);

  imm_from_sz_v_s (imm, SZ8, 7, true);
  jz (imm);

  imm_from_sz_v_s (imm, SZ32, ((is_xcmpl) ? 1 : -1), true);
  mov_r_imm (reg0, imm);
  imm_from_sz_v_s (imm, SZ8, 2, true);
  jmp_imm (imm);

  alu_r_r (xor, reg0, reg0);

  return stream;
}

static bool
fpu_lower_xcmpu (JitCompContext *cc, char **stream_ptr, JitReg r0,
                 JitReg r1, JitReg r2, bool is_double, bool is_xcmpl)
{
  char *stream = *stream_ptr;
  Imm_Opnd imm;
  R_Opnd reg0 = regs_I4[jit_reg_no (r0)];
  float f1 = 0, f2 = 0;
  double d1 = 0, d2 = 0;

  if (jit_reg_is_const (r1))
    {
      if (is_double)
        d1 = jit_cc_get_const_F8 (cc, r1);
      else
        f1 = jit_cc_get_const_F4 (cc, r1);
    }

  if (jit_reg_is_const (r2))
    {
      if (is_double)
        d2 = jit_cc_get_const_F8 (cc, r2);
      else
        f2 = jit_cc_get_const_F4 (cc, r2);
    }

  if (jit_reg_is_const (r1) && jit_reg_is_const (r2))
    {
      int32 result = 0;

      if (is_double)
        {
          if (is_xcmpl)
            result = (d1 == d2) ? 0 : (d1 > d2 ? 1 : -1);
          else
            result = (d1 == d2) ? 0 : (d1 < d2 ? -1 : 1);
        }
      else
        {
          if (is_xcmpl)
            result = (f1 == f2) ? 0 : (f1 > f2 ? 1 : -1);
          else
            result = (f1 == f2) ? 0 : (f1 < f2 ? -1 : 1);
        }

      imm_from_sz_v_s (imm, SZ32, result, true);
      mov_r_imm (reg0, imm);
      *stream_ptr = stream;
      return true;
    }

  if (jit_reg_is_const (r1))
    {
      if (is_double)
        stream = fpu_cmp_imm_double_r (stream, d1, jit_reg_no (r2));
      else
        stream = fpu_cmp_imm_float_r (stream, f1, jit_reg_no (r2));
    }
  else if (jit_reg_is_const (r2))
    {
      M_Opnd m;

      m_from_jit_cache(m);
      if (is_double) {
        MOV_IMM_F8_TO_M_Opnd(m, d2);
      } else {
        MOV_IMM_F4_TO_M_Opnd(m, f2);
      }
      stream = fpu_cmp_r_m (stream, is_double, jit_reg_no (r1), m);
    }
  else
    stream = fpu_cmp_r_r (stream, jit_reg_no (r1), jit_reg_no (r2));

  stream = fpu_lower_xcmpu_suffix (stream, r0, is_xcmpl);

  *stream_ptr = stream;
  return true;
}
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

/**
 * Encode select insn, SELECT r0, r1, r2, r3
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 *
 * @return true if success, false if failed
 */
static bool
lower_select (JitCompContext *cc, char **stream_ptr, COND_OP op,
              JitReg r0, JitReg r1, JitReg r2, JitReg r3)
{
  char *stream = *stream_ptr;
  char stream_mov1[128];
  char stream_mov2[128];
  char *stream1 = stream_mov1;
  char *stream2 = stream_mov2;

  CHECK_NCONST (r0);
  CHECK_NCONST (r1);
  CHECK_KIND (r1, JIT_REG_KIND_I4);

  if (r0 == r3 && r0 != r2)  {
      JitReg r_tmp;

      /* Exchange r2, r3*/
      r_tmp = r2;
      r2 = r3;
      r3 = r_tmp;
      op = not_cond (op);
    }

  if (!lower_mov(cc, &stream1, r0, r2))
    GOTO_FAIL;
  if (!lower_mov(cc, &stream2, r0, r3))
    GOTO_FAIL;

  if (r0 != r2)
    {
      memcpy (stream, stream_mov1, (int32)(stream1 - stream_mov1));
      stream += (int32)(stream1 - stream_mov1);
    }

  if (r3 && r0 != r3)
    {
        stream = cmp_r_and_jmp_relative (stream, jit_reg_no (r1), op,
            (int32)(stream2 - stream_mov2));
        memcpy (stream, stream_mov2, (int32)(stream2 - stream_mov2));
        stream += (int32)(stream2 - stream_mov2);
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode branch insn, BEQ/BNE/../BLTU r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param r0 dst jit register that contains the dst operand info
 * @param r1 src jit register that contains the first src operand info
 * @param r2 src jit register that contains the second src operand info
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
lower_branch (JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
              int32 label_src, COND_OP op, JitReg r0, JitReg r1, JitReg r2,
              bool is_last_insn)
{
  int32 reg_no, label_dst;
  char *stream = *stream_ptr;

  CHECK_NCONST (r0);
  CHECK_KIND (r0, JIT_REG_KIND_I4);
  CHECK_KIND (r1, JIT_REG_KIND_L4);

  label_dst = jit_reg_no (r1);
  if (label_dst < (int32)jit_cc_label_num (cc) - 1 &&
      is_last_insn &&
      label_is_neighboring (cc, label_src, label_dst))
    {
      JitReg r_tmp;

      r_tmp = r1;
      r1 = r2;
      r2 = r_tmp;
      op = not_cond (op);
    }

  reg_no = jit_reg_no (r0);
  if (!cmp_r_and_jmp_label (cc, &stream, stream_offset, label_src,
                            op, reg_no, r1, r2, is_last_insn))
    GOTO_FAIL;

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/* jmp to dst label */
#define JMP_TO_LABEL(stream_offset, label_dst, label_src)   \
  do {                                                      \
    if (label_is_ahead (cc, label_dst, label_src)) {        \
      int32 _offset;                                        \
      _offset = label_get_offset (cc, label_dst, label_src, \
                                  stream_offset);           \
      jmp_offset (_offset);                                 \
    }                                                       \
    else {                                                  \
      if (!jmp_from_label_to_label (&stream, stream_offset, \
                                    label_dst, label_src))  \
        GOTO_FAIL;                                          \
    }                                                       \
  } while (0)

/* jmp to dst label */
#define JMP_TO_LABEL_WITHOUT_REFINE(stream_offset, label_dst, label_src)\
  do {                                                      \
    if (!jmp_from_label_to_label (&stream, stream_offset,   \
                                  label_dst, label_src))    \
        GOTO_FAIL;                                          \
  } while (0)

/**
 * Encode detecting tableswitch entry register and jumping to matched label
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param reg_no the no of entry register
 * @param opnd the table switch operand
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
tableswitch_r (JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
               int32 label_src, int32 reg_no, const JitOpndTableSwitch *opnd,
               bool is_last_insn)
{
  JmpInfo *node;
  Imm_Opnd imm;
  int32 i, label_dst, offset;
  char *stream;
  uint32 stream_offset_new;

  stream = *stream_ptr;

  if (opnd->low_value != opnd->high_value)
    {
      imm_from_sz_v_s (imm, SZ32, opnd->low_value, true);
      alu_r_imm (cmp, regs_I4[reg_no], imm);
      /* 0x25 is length of stream 1 and stream 2 */
      offset = 0x25 + 5 * (opnd->high_value - opnd->low_value + 1);
      if (offset <= 127)
        imm_from_sz_v_s (imm, SZ8, offset, true);
      else
        imm_from_sz_v_s (imm, SZ32, offset, true);
      jl (imm);

      /* stream 1 begin */
      imm_from_sz_v_s (imm, SZ32, opnd->high_value, true);
      alu_r_imm (cmp, regs_I4[reg_no], imm);
      imm_from_sz_v_s (imm, SZ32,
                       0x19 + 5 *(opnd->high_value - opnd->low_value + 1),
                       true);
      /* 0x19 is length of stream 2 */
      jg (imm);

      /* stream 2 begin */
      push_r (regs_I4[reg_no]);
      imm_from_sz_v_s (imm, SZ32, opnd->low_value, true);
      alu_r_imm (sub, regs_I4[reg_no], imm);
      mov_r_r (reg_I4_free, regs_I4[reg_no]);
      imm_from_sz_v_s (imm, SZ32, 2, true);
      shift_r_imm (shl, reg_I4_free, imm);
      alu_r_r (add, reg_I4_free, regs_I4[reg_no]);
      pop_r (regs_I4[reg_no]);

      node = jit_malloc (sizeof (JmpInfo));
      if (!node)
        GOTO_FAIL;

      node->type = JMP_TABLE_SWITCH;
      node->label_src = label_src;
      node->offset = stream + 2 - (*stream_ptr - stream_offset);
      bh_list_insert (jmp_info_list, node);

      imm_from_sz_v_s (imm, SZ32, (int32)stream + 11, true);
      alu_r_imm (add, reg_I4_free, imm);

      jmp_r (reg_I4_free);

      /* stream 3 begin */
      for (i = opnd->low_value; i <= opnd->high_value; i++)
        {
          label_dst = jit_reg_no (opnd->targets[i - opnd->low_value]);
          stream_offset_new = stream_offset + stream - *stream_ptr;
          if ( !( i == opnd->high_value &&
                  !opnd->default_target &&
                  is_last_insn &&
                  label_is_neighboring (cc, label_src, label_dst) ) )
            JMP_TO_LABEL_WITHOUT_REFINE (stream_offset_new,
                                         label_dst, label_src);
        }
    }
  else /* low_value == high_value, only has a branch */
    {
      label_dst = jit_reg_no (opnd->targets[0]);

      if ( !( !opnd->default_target &&
              is_last_insn &&
              label_is_neighboring (cc, label_src, label_dst) ) )
        {
          imm_from_sz_v_s (imm, SZ32, opnd->low_value, true);
          alu_r_imm (cmp, regs_I4[reg_no], imm);

          node = jit_malloc (sizeof (JmpInfo));
          if (!node)
            GOTO_FAIL;

          node->type = JMP_DST_LABEL;
          node->label_src = label_src;
          node->dst_info.label_dst = label_dst;
          node->offset = stream + 2 - (*stream_ptr - stream_offset);
          bh_list_insert (jmp_info_list, node);

          imm_from_sz_v_s (imm, SZ32, label_dst, true);
          je (imm);
        }
    }

  stream_offset_new = stream_offset + stream - *stream_ptr;
  if (opnd->default_target)
    {
      label_dst = jit_reg_no (opnd->default_target);
      if ( !( is_last_insn && label_is_neighboring (cc, label_src, label_dst) ) )
        JMP_TO_LABEL (stream_offset_new, label_dst, label_src);
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode tableswitch insn, TABLESWITCH opnd
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param opnd the table switch operand
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
lower_tableswitch (JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
                   int32 label_src, const JitOpndTableSwitch *opnd,
                   bool is_last_insn)
{
  JitReg r0 = opnd->value;
  int32 reg_no, label_dst;
  char *stream = *stream_ptr;

  CHECK_KIND (r0, JIT_REG_KIND_I4);

  if (jit_reg_is_const (r0))
    {
      int32 data = jit_cc_get_const_I4 (cc, r0);

      if (data < opnd->low_value || data > opnd->high_value)
        {
          if (opnd->default_target)
            {
              label_dst = jit_reg_no (opnd->default_target);
              if ( !( is_last_insn &&
                      label_is_neighboring (cc, label_src, label_dst) ) )
                JMP_TO_LABEL (stream_offset, label_dst, label_src);
            }
        }
      else
        {
          label_dst = jit_reg_no (opnd->targets[data - opnd->low_value]);
          if ( !( is_last_insn &&
                label_is_neighboring (cc, label_src, label_dst) ) )
            JMP_TO_LABEL (stream_offset, label_dst, label_src);
        }
    }
  else
    {
      reg_no = jit_reg_no (r0);
      if (!tableswitch_r (cc, &stream, stream_offset, label_src,
                          reg_no, opnd, is_last_insn))
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode lookupswitch with key of immediate data
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param key the entry key
 * @param opnd the lookup switch operand
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
lookupswitch_imm (JitCompContext *cc, char **stream_ptr,
                  uint32 stream_offset, int32 label_src,
                  int32 key, const JitOpndLookupSwitch *opnd,
                  bool is_last_insn)
{
  uint32 i;
  int32 label_dst;
  char *stream;

  stream = *stream_ptr;

  for (i = 0; i < opnd->match_pairs_num; i++)
    if (key == opnd->match_pairs[i].value)
      {
        label_dst = jit_reg_no (opnd->match_pairs [i].target);
        if ( !( is_last_insn &&
                label_is_neighboring (cc, label_src, label_dst) ) )
          JMP_TO_LABEL (stream_offset, label_dst, label_src);

        *stream_ptr = stream;
        return true;
      }

  if (opnd->default_target)
    {
      label_dst = jit_reg_no (opnd->default_target);
      if ( !( is_last_insn &&
              label_is_neighboring (cc, label_src, label_dst) ) )
        JMP_TO_LABEL (stream_offset, label_dst, label_src);
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode detecting lookupswitch entry register and jumping to matched label
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param reg_no the no of entry register
 * @param opnd the lookup switch operand
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
lookupswitch_r (JitCompContext *cc, char **stream_ptr,
                uint32 stream_offset, int32 label_src,
                int32 reg_no, const JitOpndLookupSwitch *opnd,
                bool is_last_insn)
{
  JmpInfo *node;
  Imm_Opnd imm;
  uint32 i, stream_offset_new;
  int32 label_dst;
  char *stream;

  stream = *stream_ptr;

  for (i = 0; i < opnd->match_pairs_num; i++)
    {
      imm_from_sz_v_s (imm, SZ32, opnd->match_pairs[i].value, true);
      alu_r_imm (cmp, regs_I4[reg_no], imm);

      label_dst = jit_reg_no (opnd->match_pairs [i].target);
      imm_from_sz_v_s (imm, SZ32, label_dst, true);

      node = jit_malloc (sizeof (JmpInfo));
      if (!node)
        GOTO_FAIL;

      node->type = JMP_DST_LABEL;
      node->label_src = label_src;
      node->dst_info.label_dst = label_dst;
      node->offset = (int32) (stream + 2 - (*stream_ptr - stream_offset));
      bh_list_insert (jmp_info_list, node);

      je (imm);
    }

  if (opnd->default_target)
    {
      label_dst = jit_reg_no (opnd->default_target);
      stream_offset_new = stream_offset + stream - *stream_ptr;
      if ( !( is_last_insn &&
              label_is_neighboring (cc, label_src, label_dst) ) )
        JMP_TO_LABEL (stream_offset_new, label_dst, label_src);
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode lookupswitch insn, LOOKUPSWITCH opnd
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param opnd the lookup switch operand
 * @param is_last_insn if current insn is the last insn of current block
 *
 * @return true if success, false if failed
 */
static bool
lower_lookupswitch (JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
                   int32 label_src, const JitOpndLookupSwitch *opnd,
                   bool is_last_insn)
{
  JitReg r0 = opnd->value;
  int32 key, reg_no;
  char *stream = *stream_ptr;

  CHECK_KIND (r0, JIT_REG_KIND_I4);
  CHECK_KIND (opnd->default_target, JIT_REG_KIND_L4);

  if (jit_reg_is_const (r0))
    {
      key = jit_cc_get_const_I4 (cc, r0);
      if (!lookupswitch_imm (cc, &stream, stream_offset, label_src,
                             key, opnd, is_last_insn))
        GOTO_FAIL;
    }
  else
    {
      reg_no = jit_reg_no (r0);
      if (!lookupswitch_r (cc, &stream, stream_offset, label_src,
                           reg_no, opnd, is_last_insn))
        GOTO_FAIL;
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}


#ifdef CODEGEN_DUMP_LOWER_RESULT
static void
dump_stream (char *addr, int32 length)
{
  char buf[256];
  char *stream = addr;

  stream = addr;
  if (length > 0)
    {
      while ( stream - addr < length)
        {
          stream = decoder_disassemble_instr(stream, buf, 256);
          jit_printf ("        %s\n", buf);
        }
      jit_printf ("\n");
    }
}
#endif /* end of CODEGEN_DUMP_LOWER_RESULT */

/* The start operand index of argument in callnative operand list */
#define NATIVE_ARG_START_INDEX    2

/**
 * Encode pushing all arguments of native function
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param insn current insn info
 * @param args_num_pushed return the number of arguments pushed
 * @param global_offset_base the base for calculating global offset
 *
 * @return true if success, false if failed
 */
static bool
push_native_args(JitCompContext *cc, char **stream_ptr, JitInsn *insn,
                 uint32 *args_num_pushed, unsigned global_offset_base)
{
  Imm_Opnd imm;
  char *stream;
  uint32 i, ni = 0;
  uint32 opnd_num = jit_insn_opndv_num (insn);
  JitReg r0;
  int32 data;
  int64 data_int64;

  stream = *stream_ptr;
  for (i = opnd_num - 1; i >= NATIVE_ARG_START_INDEX; i--)
    {
      r0 = *(jit_insn_opndv (insn, i));
      switch (jit_reg_kind (r0))
        {
          case JIT_REG_KIND_I4:
            if (jit_reg_is_const (r0))
              {
                unsigned rel;
                data = jit_cc_get_const_I4 (cc, r0);
                imm_from_sz_v_s (imm, SZ32, data, true);
                push_imm (imm);

                if ((rel = jit_cc_get_const_I4_rel (cc, r0))) {
                  add_aot_reloc_record (EncoderBase_curRealOpnd[0].size,
                                        ((uint32)EncoderBase_curRealOpnd[0].pos
                                         + global_offset_base), rel);
                }
              }
            else
              push_r (regs_I4[jit_reg_no (r0)]);

            ni ++;
            break;

          case JIT_REG_KIND_I8:
            if (!jit_reg_is_const (r0))
              {
                LOG_VERBOSE ("unsupported reg kind got : %d\n",
                            jit_reg_kind(r0));
                GOTO_FAIL;
              }
            data_int64 = jit_cc_get_const_I8 (cc, r0);
            data = (int32)(data_int64 >> 32);
            imm_from_sz_v_s (imm, SZ32, data, true);
            push_imm (imm);

            data = (int32)data_int64;
            imm_from_sz_v_s (imm, SZ32, data, true);
            push_imm (imm);

            ni += 2;
            break;

          default:
            LOG_VERBOSE ("unsupported reg kind got : %d\n",
                        jit_reg_kind(r0));
            GOTO_FAIL;
        }
    }

  *args_num_pushed = ni;
  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Encode callnative insn, CALLNATIVE r0, r1, ...
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param insn current insn info
 * @param global_offset_base the base for calculating global offset
 *
 * @return true if success, false if failed
 */
static bool
lower_callnative(JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
                 int32 label_src, JitInsn *insn, unsigned global_offset_base)
{
  char *stream;
  uint32 args_num_pushed;
  int32 (*func_ptr)();
  JitReg ret_reg, func_reg;
  Imm_Opnd imm;
  JmpInfo *node;
  unsigned rel;

  stream = *stream_ptr;

  ret_reg = *(jit_insn_opndv (insn, 0));
  func_reg = *(jit_insn_opndv (insn, 1));
  CHECK_KIND (func_reg, JIT_REG_KIND_I4);
  if (jit_reg_is_const (func_reg))
    func_ptr = (int32(*)()) (jit_cc_get_const_I4 (cc, func_reg));

  if (!push_native_args(cc, &stream, insn, &args_num_pushed, global_offset_base))
    GOTO_FAIL;

  if (jit_reg_is_const (func_reg)) {
      node = jit_malloc (sizeof (JmpInfo));
      if (!node)
        GOTO_FAIL;

      node->type = JMP_TARGET_CODE;
      node->label_src = label_src;
      node->offset = (int32) (stream + 1 - (*stream_ptr - stream_offset));
      node->dst_info.target_code_addr = (int32)func_ptr;
      bh_list_insert (jmp_info_list, node);

      imm_from_sz_v_s (imm, SZ32, (int32)func_ptr, true);
      call_imm (imm);

    if ((rel = jit_cc_get_const_I4_rel (cc, func_reg))) {
      add_aot_reloc_record (EncoderBase_curRealOpnd[0].size | AOT_RELOC_JMP_TARGET_CODE,
                            ((uint32)EncoderBase_curRealOpnd[0].pos
                             + global_offset_base), rel);
    }
  }
  else
    call_r (regs_I4[jit_reg_no (func_reg)]);

  if (ret_reg)
    mov_r_r (regs_I4[jit_reg_no (ret_reg)], eax);

  if (args_num_pushed)
    {
      imm_from_sz_v_s (imm, SZ32, args_num_pushed * 4, true);
      alu_r_imm (add, esp, imm);
    }

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

static int32 length_of_callbc_jmp = 0;

/**
 * Encode callbc insn, CALLBC r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param insn current insn info
 * @param global_offset_base the base for calculating global offset
 *
 * @return true if success, false if failed
 */
static bool
lower_callbc(JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
             int32 label_src, JitInsn *insn, unsigned global_offset_base)
{
  JmpInfo *node;
  char *stream, *stream_before_jmp;
  M_Opnd m;
  Imm_Opnd imm;
  JitReg ecx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_ECX_INDEX);
  JitReg edx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_EDX_INDEX);
  JitReg ret_reg1 = *(jit_insn_opnd (insn, 0));
  JitReg ret_reg2 = *(jit_insn_opnd (insn, 1));
  JitReg jmethod_reg = *(jit_insn_opnd (insn, 2));

  CHECK_KIND (jmethod_reg, JIT_REG_KIND_I4);

  stream = *stream_ptr;

  /* Load glue_ret_method from stack */
  if (!jit_reg_is_const (jmethod_reg))
    mov_r_r (eax, regs_I4[jit_reg_no (jmethod_reg)]);
  else
    {
      unsigned rel;
      imm_from_sz_v_s (imm, SZ32,
                       jit_cc_get_const_I4 (cc, jmethod_reg),
                       true);
      mov_r_imm (eax, imm);

      if ((rel = jit_cc_get_const_I4_rel (cc, jmethod_reg))){
        add_aot_reloc_record (EncoderBase_curRealOpnd[1].size,
                              ((uint32)EncoderBase_curRealOpnd[1].pos
                               + global_offset_base), rel);
      }
    }

  /* Load return_jited_addr from stack */
  m_from_b_d (m, ebp_reg, cc->jited_return_address_offset);

  node = jit_malloc (sizeof (JmpInfo));
  if (!node)
    GOTO_FAIL;

  node->type = JMP_END_OF_CALLBC;
  node->label_src = label_src;
  if ( (uint32)cc->jited_return_address_offset < 0x80)
    node->offset = (int32) (stream + 3 - (*stream_ptr - stream_offset));
  else
    node->offset = (int32) (stream + 6 - (*stream_ptr - stream_offset));
  bh_list_insert (jmp_info_list, node);

  /**
   * Set next jited addr to glue_ret_jited_addr,
   * 0 will be replaced with actual offset after
   * actual code cache is allocated
   */
  imm_from_sz_v_s (imm, SZ32, 0, true);
  mov_m_imm (m, imm);

  add_aot_reloc_record (EncoderBase_curRealOpnd[1].size | AOT_RELOC_RETURN_ADDRESS,
                        ((uint32)EncoderBase_curRealOpnd[1].pos
                         + global_offset_base), 0);

  stream_before_jmp = stream;

  m_from_b_d (m, eax_reg, 0);
  jmp_m (m);

  length_of_callbc_jmp = (int32) (stream - stream_before_jmp);

  if (ret_reg1)
    {
      switch (jit_reg_kind (ret_reg1))
        {
          case JIT_REG_KIND_I4:
            if (!ret_reg2)
              {
                if (!lower_mov (cc, &stream, ret_reg1, ecx_hreg))
                  GOTO_FAIL;
              }
            else
              {
                jit_assert (jit_reg_is_kind (I4, ret_reg2));

                if (ret_reg1 != edx_hreg)
                  {
                    if (!(lower_mov (cc, &stream, ret_reg1, ecx_hreg) &&
                          lower_mov (cc, &stream, ret_reg2, edx_hreg)))
                      GOTO_FAIL;
                  }
                else if (ret_reg2 != ecx_hreg)
                  {
                    if (!(lower_mov (cc, &stream, ret_reg2, edx_hreg) &&
                          lower_mov (cc, &stream, ret_reg1, ecx_hreg)))
                      GOTO_FAIL;
                  }
                else
                  {
                    /* exchange edx, ecx */
                    push_r (edx);
                    mov_r_r (edx, ecx);
                    pop_r (ecx);
                  }
              }
            break;
#ifdef CODEGEN_ENABLE_FLOATING_POINT
          case JIT_REG_KIND_F4:
            if (!lower_mov (cc, &stream, ret_reg1, jit_reg_new (JIT_REG_KIND_F4, 0)))
              GOTO_FAIL;
            break;
          case JIT_REG_KIND_F8:
            if (!lower_mov (cc, &stream, ret_reg1, jit_reg_new (JIT_REG_KIND_F8, 0)))
              GOTO_FAIL;
            break;
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
          default:
            GOTO_FAIL;
        }
    }

  *stream_ptr = stream;
  return true;

fail:
  return false;
}

/**
 * Encode returnbc insn, RETURNBC r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param insn current insn info
 *
 * @return true if success, false if failed
 */
#if BEIHAI_ENABLE_JIT_LLVM == 0
static bool
lower_returnbc(JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
               int32 label_src, JitInsn *insn)
{
  char *stream;
  int32 act;
  M_Opnd m;
  Imm_Opnd imm;
  JitReg ecx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_ECX_INDEX);
  JitReg edx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_EDX_INDEX);
  JitReg act_reg = *(jit_insn_opnd (insn, 0));
  JitReg ret_reg1 = *(jit_insn_opnd (insn, 1));
  JitReg ret_reg2 = *(jit_insn_opnd (insn, 2));

  CHECK_CONST (act_reg);
  CHECK_KIND (act_reg, JIT_REG_KIND_I4);

  stream = *stream_ptr;
  act = jit_cc_get_const_I4 (cc, act_reg);

  if (ret_reg1)
    {
      if (jit_reg_is_kind (I4, ret_reg1))
        {
          if (!ret_reg2)
            {
              if (!lower_mov (cc, &stream, ecx_hreg, ret_reg1))
                GOTO_FAIL;
            }
          else
            {
              jit_assert (jit_reg_is_kind (I4, ret_reg2));

              if (ret_reg2 != ecx_hreg)
                {
                  if (!(lower_mov (cc, &stream, ecx_hreg, ret_reg1) &&
                        lower_mov (cc, &stream, edx_hreg, ret_reg2)))
                    GOTO_FAIL;
                }
              else if (ret_reg1 != edx_hreg)
                {
                  if (!(lower_mov (cc, &stream, edx_hreg, ret_reg2) &&
                        lower_mov (cc, &stream, ecx_hreg, ret_reg1)))
                    GOTO_FAIL;
                }
              else
                {
                  /* exchange edx, ecx */
                  push_r (edx);
                  mov_r_r (edx, ecx);
                  pop_r (ecx);
                }
            }
        }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
      else if (jit_reg_is_kind (F4, ret_reg1))
        {
          if (!lower_mov (cc, &stream, jit_reg_new (JIT_REG_KIND_F4, 0), ret_reg1))
            GOTO_FAIL;
        }
      else if (jit_reg_is_kind (F8, ret_reg1))
        {
          if (!lower_mov (cc, &stream, jit_reg_new (JIT_REG_KIND_F8, 0), ret_reg1))
            GOTO_FAIL;
        }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
      else
        GOTO_FAIL;
    }

  /* eax = act */
  imm_from_sz_v_s (imm, SZ32, act, true);
  mov_r_imm (eax, imm);
  m_from_b_d (m, ebp_reg, cc->jited_return_address_offset);
  jmp_m (m);

  *stream_ptr = stream;
  return true;

fail:
  return false;
}
#else
static bool
lower_returnbc(JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
               int32 label_src, JitInsn *insn)
{
  char *stream;
  int32 act;
  M_Opnd m;
  Imm_Opnd imm;
  JitReg act_reg = *(jit_insn_opnd (insn, 0));
  JitReg ret_reg1 = *(jit_insn_opnd (insn, 1));
  JitReg ret_reg2 = *(jit_insn_opnd (insn, 2));
  JitReg prev_frame = *(jit_insn_opnd (insn, 3));

  CHECK_CONST (act_reg);
  CHECK_KIND (act_reg, JIT_REG_KIND_I4);

  stream = *stream_ptr;

  /* reg_I4_free = info */
  m_from_b_d (m, esp_reg, 16 + 8);
  mov_r_m (reg_I4_free, m);
  /* info->frame = prev_frame */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0);
  mov_m_r (m, regs_I4[jit_reg_no (prev_frame)]);

  if (ret_reg1)
    {
      if (jit_reg_is_kind (I4, ret_reg1))
        {
          /* info->out.ret.ival[0] = ret1 */
          m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 4);
          mov_m_r (m, regs_I4[jit_reg_no (ret_reg1)]);

          if (ret_reg2)
            {
              /* info->out.ret.ival[1] = ret2 */
              m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 8);
              mov_m_r (m, regs_I4[jit_reg_no (ret_reg2)]);
            }
        }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
      else if (jit_reg_is_kind (F4, ret_reg1))
        {
          /* info->out.ret.fval[0] = ret1 */
          if (!lower_mov (cc, &stream, jit_reg_new (JIT_REG_KIND_F4, 0), ret_reg1))
            GOTO_FAIL;
          m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0xC);
          fst_m (m);
        }
      else if (jit_reg_is_kind (F8, ret_reg1))
      {
        /* info->out.ret.fval[0, 1] = ret1 */
        if (!lower_mov (cc, &stream, jit_reg_new (JIT_REG_KIND_F8, 0), ret_reg1))
          GOTO_FAIL;
        m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0xC);
        dst_m (m);
      }
#endif
    }

  /* eax = act */
  act = jit_cc_get_const_I4 (cc, act_reg);
  imm_from_sz_v_s (imm, SZ32, act, true);
  mov_r_imm (eax, imm);

  ENCODER_FILL_END ();
  *stream_ptr = stream;
  return true;
fail:
  return false;
}
#endif

/**
 * Encode leave insn, LEAVE r0, r1, r2
 *
 * @param cc the compiler context
 * @param stream_ptr pointer container contains current
 *        native code stream, and return the new stream
 * @param stream_offset offset to the beginning of native code
 * @param label_src the index of src label
 * @param insn current insn info
 * @param global_offset_base the base for calculating global offset
 *
 * @return true if success, false if failed
 */
static bool
lower_leave(JitCompContext *cc, char **stream_ptr, uint32 stream_offset,
            int32 label_src, JitInsn *insn, unsigned global_offset_base)
{
  JmpInfo *node;
  char *stream, *code_block;
  int32 act;
  Imm_Opnd imm;
  JitReg act_reg = *(jit_insn_opnd (insn, 0));
  JitReg ip_reg = *(jit_insn_opnd (insn, 1));
  JitReg sp_or_index_reg = *(jit_insn_opnd (insn, 2));

  CHECK_CONST (act_reg);
  CHECK_KIND (act_reg, JIT_REG_KIND_I4);

  stream = *stream_ptr;
  act = jit_cc_get_const_I4 (cc, act_reg);
  code_block = interp_action_to_code_block (act);

  if (ip_reg)
    {
      imm_from_sz_v_s (imm, SZ32, jit_cc_get_const_I4 (cc, ip_reg), true);
      mov_r_imm (ecx, imm);
    }

  if (sp_or_index_reg)
    {
      imm_from_sz_v_s (imm, SZ32, jit_cc_get_const_I4 (cc, sp_or_index_reg), true);
      mov_r_imm (edx, imm);
    }

  node = jit_malloc (sizeof (JmpInfo));
  if (!node)
    GOTO_FAIL;

  node->type = JMP_TARGET_CODE;
  node->label_src = label_src;
  node->offset = (int32) (stream + 1 - (*stream_ptr - stream_offset));
  node->dst_info.target_code_addr = (int32)code_block;
  bh_list_insert (jmp_info_list, node);
  imm_from_sz_v_s (imm, SZ32, 0, true);
  jmp_imm (imm);

  add_aot_reloc_record ((EncoderBase_curRealOpnd[0].size
                         | AOT_RELOC_JMP_TARGET_CODE
                         | AOT_RELOC_CODE_BLOCK),
                        ((uint32)EncoderBase_curRealOpnd[0].pos
                         + global_offset_base), act);

  *stream_ptr = stream;
  return true;

fail:

  return false;
}

/**
 * Replace all the jmp address pre-saved when the code cache hasn't been
 * allocated with actual address after code cache allocated
 *
 * @param cc compiler context containting the allocated code cacha info
 */
static void
replace_jmp_addr_from_virtual_to_absolute (JitCompContext *cc)
{
  void* cur_node = bh_list_first_elem(jmp_info_list);
  while (cur_node)
    {
      void *next_node = bh_list_elem_next(cur_node);
      JmpInfo *node = (JmpInfo*) cur_node;
      JitReg reg_src = jit_reg_new (JIT_REG_KIND_L4, node->label_src);
      char *stream_src = (char*)*jit_annl_jited_addr (cc, reg_src);
      char *stream = stream_src + node->offset;

      if (node->type == JMP_DST_LABEL)
        {
          JitReg reg_dst = jit_reg_new (JIT_REG_KIND_L4,
                                        node->dst_info.label_dst);
          *(int32*)stream = (int32)*jit_annl_jited_addr (cc, reg_dst) -
                            (int32)stream - 4;
        }
      else if (node->type == JMP_END_OF_CALLBC)
        *(int32*)stream = (int32)stream + 4 + length_of_callbc_jmp;
      else if (node->type == JMP_TABLE_SWITCH)
        *(int32*)stream = (int32)stream + 6;
      else if (node->type == JMP_TARGET_CODE)
        *(int32*)stream = node->dst_info.target_code_addr - (int32) stream - 4;

      bh_list_remove (jmp_info_list, cur_node);
      jit_free (cur_node);
      cur_node = next_node;
    }
}

/* Free the jmp info list */
static void
free_jmp_info_list()
{
  void* cur_node = bh_list_first_elem(jmp_info_list);
  while (cur_node)
    {
      void *next_node = bh_list_elem_next(cur_node);

      bh_list_remove (jmp_info_list, cur_node);
      jit_free (cur_node);
      cur_node = next_node;
    }
}

#define MAX_STATIC_CACHE_NUM    4
#define MAX_STREAM_CACHE_NUM    50
#define MAX_STREAM_CACHE_SIZE   1024
#define MIN_INSN_STREAM_LENGTH  64

static char stream_cache[MAX_STATIC_CACHE_NUM][MAX_STREAM_CACHE_SIZE];

bool
jit_codegen_x86_gen_native (JitCompContext *cc)
{
  int32 label_index, label_num, i, j;
  JitBlock *block;
  JitInsn *insn;
  JitReg r0, r1, r2, r3;
  char *cache_list[MAX_STREAM_CACHE_NUM], *stream;
  int32 cache_size[MAX_STREAM_CACHE_NUM];
  int32 cache_num, cache_index, stream_offset;
  int32 total_stream_size, cur_label_stream_size, size_needed;
  void **jited_addr;
  bool return_value = true;
  bool is_last_insn;
  void *reloc_info = NULL;
  JitReg real_opnd_to_reg[3];
#ifdef CODEGEN_DUMP_LOWER_RESULT
  char *stream_last;
#endif

  if (BH_LIST_SUCCESS != bh_list_init (jmp_info_list))
    return false;

  memset(cache_list, 0, sizeof(cache_list));
  cache_num = MAX_STATIC_CACHE_NUM;
  for (i =0; i < MAX_STATIC_CACHE_NUM; i ++)
    cache_list[i] = stream_cache[i];

  total_stream_size = 0;
  cur_aot_reloc_record_index = 0;

  label_num = jit_cc_label_num (cc);

  stream_list = jit_malloc (label_num * sizeof (StreamInfo));
  if (!stream_list)
    return false;
  memset (stream_list, 0, label_num * sizeof (StreamInfo));

#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("V1.Jit code begin, method: ");
  jit_frontend_print_method_name (cc->method);
  jit_printf ("\n\n");
#endif
  for (i = 0; i < label_num; i++ )
    {
      if (i > 0 && i < label_num - 1)
        label_index = i + 1;
      else if (i == 0)
        label_index = 0;
      else
        label_index = 1;

      block = *jit_annl_block (cc, jit_reg_new (JIT_REG_KIND_L4, label_index));

      cur_label_stream_size = 0;
      cache_index = 0;
      stream = cache_list[cache_index];

#if BEIHAI_ENABLE_JIT_LLVM != 0
      if (label_index == 0)
        ENCODER_FILL_START ();
#endif

#ifdef CODEGEN_DUMP_LOWER_RESULT
      jit_printf ("L%d:\n", label_index);
#endif
#ifdef CODEGEN_TRACE_EXEC_RESULT
      DUMP_INSN_LABEL (label_index);
#endif

      JIT_FOREACH_INSN (block, insn)
        {
          is_last_insn = (insn->next == block) ? true : false;

          memset (real_opnd_to_reg, 0, sizeof (real_opnd_to_reg));

#ifdef CODEGEN_TRACE_EXEC_RESULT
          if (insn->opcode == JIT_OP_JMP ||
              insn->opcode == JIT_OP_TABLESWITCH ||
              insn->opcode == JIT_OP_LEAVE ||
              (insn->opcode >= JIT_OP_BEQ && insn->opcode <= JIT_OP_BLEU))
            DUMP_INSN (cc, insn);
#endif
          size_needed = MIN_INSN_STREAM_LENGTH;
          if (insn->opcode == JIT_OP_TABLESWITCH)
            {
              JitOpndTableSwitch *opnd = jit_insn_opndts (insn);
              size_needed += (opnd->high_value - opnd->low_value  + 1) * 5;
            }
          else if (insn->opcode == JIT_OP_LOOKUPSWITCH)
            {
              JitOpndLookupSwitch *opnd = jit_insn_opndls (insn);
              size_needed += opnd->match_pairs_num  * 6;
            }
          if (MAX_STREAM_CACHE_SIZE - (stream - cache_list[cache_index]) <
              size_needed)
            {
              cache_size[cache_index] = stream - cache_list[cache_index];
              cur_label_stream_size += cache_size[cache_index];

              cache_index ++;
              if (cache_index >= cache_num)
                {
                  if (cache_num >= MAX_STREAM_CACHE_NUM)
                    GOTO_FAIL;
                  cache_list[cache_num] = jit_malloc (MAX_STREAM_CACHE_SIZE);
                  if (!cache_list[cache_num])
                    GOTO_FAIL;
                  cache_num ++;
                }
              stream = cache_list[cache_index];
            }

#ifdef CODEGEN_DUMP_LOWER_RESULT
          jit_dump_insn (cc, insn);
          stream_last = stream;
#endif

          stream_offset = cur_label_stream_size + stream -
                          cache_list[cache_index];
          switch (insn->opcode)
            {
            case JIT_OP_MOV:
              LOAD_2ARGS;
              if (!lower_mov (cc, &stream, r0, r1))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_I4TOI1:
              LOAD_2ARGS;
              CONVERT_R_R (I4, I4, int8, int32);
              BREAK;

            case JIT_OP_I4TOU1:
              LOAD_2ARGS;
              CONVERT_R_R (I4, I4, uint8, int32);
              BREAK;

            case JIT_OP_I4TOI2:
              LOAD_2ARGS;
              CONVERT_R_R (I4, I4, int16, int32);
              BREAK;

            case JIT_OP_I4TOU2:
              LOAD_2ARGS;
              CONVERT_R_R (I4, I4, uint16, int32);
              BREAK;

#ifdef CODEGEN_ENABLE_FLOATING_POINT
            case JIT_OP_I4TOF4:
            case JIT_OP_U4TOF4:
              LOAD_2ARGS;
              CONVERT_R_R (F4, I4, float, int32);
              BREAK;

            case JIT_OP_I4TOF8:
            case JIT_OP_U4TOF8:
              LOAD_2ARGS;
              CONVERT_R_R (F8, I4, double, int32);
              BREAK;

            case JIT_OP_F4TOI4:
              LOAD_2ARGS;
              CONVERT_R_R (I4, F4, int32, float);
              BREAK;

            case JIT_OP_F4TOF8:
              LOAD_2ARGS;
              CONVERT_R_R (F8, F4, double, float);
              BREAK;

            case JIT_OP_F8TOI4:
              LOAD_2ARGS;
              CONVERT_R_R (I4, F8, int32, double);
              BREAK;

            case JIT_OP_F8TOF4:
              LOAD_2ARGS;
              CONVERT_R_R (F4, F8, float, double);
              BREAK;
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

            case JIT_OP_NEG:
              LOAD_2ARGS;
              if (!lower_neg (cc, &stream, r0, r1))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_ADD:
            case JIT_OP_SUB:
            case JIT_OP_MUL:
            case JIT_OP_DIV:
            case JIT_OP_REM:
              LOAD_3ARGS;
              if (!lower_alu (cc, &stream,
                              ADD + (insn->opcode - JIT_OP_ADD),
                              r0, r1, r2))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_SHL:
            case JIT_OP_SHRS:
            case JIT_OP_SHRU:
              LOAD_3ARGS;
              if (!lower_shift (cc, &stream,
                                SHL + (insn->opcode - JIT_OP_SHL),
                                r0, r1, r2))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_OR:
            case JIT_OP_XOR:
            case JIT_OP_AND:
              LOAD_3ARGS;
              if (!lower_bit (cc, &stream,
                              OR + (insn->opcode -JIT_OP_OR),
                              r0, r1, r2))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_CMP:
              LOAD_3ARGS;
              if (!lower_cmp (cc, &stream, r0, r1, r2))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_XCMPLS:
            case JIT_OP_XCMPLU:
            case JIT_OP_XCMPGS:
            case JIT_OP_XCMPGU:
              LOAD_3ARGS;
              if (jit_reg_kind (r1) == JIT_REG_KIND_I4)
                {
                  bool is_signed = true;

                  if (insn->opcode == JIT_OP_XCMPLU ||
                      insn->opcode == JIT_OP_XCMPGU)
                    is_signed = false;

                  /* xcmpl(s/u) is same as xcmpg(s/u) for int32  */
                  if (!lower_xcmpl_int32 (cc, &stream, r0, r1, r2, is_signed))
                    GOTO_FAIL;
                }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
              else if (jit_reg_kind (r1) == JIT_REG_KIND_F4 ||
                       jit_reg_kind (r1) == JIT_REG_KIND_F8)
                {
                  bool is_double = (jit_reg_kind (r1) == JIT_REG_KIND_F8);
                  bool is_xcmpl = true;

                  if (insn->opcode == JIT_OP_XCMPLS ||
                      insn->opcode == JIT_OP_XCMPGS)
                    /* should not use signed compare for float/double */
                    GOTO_FAIL;

                  if (insn->opcode == JIT_OP_XCMPGU)
                    {
                      JitReg r_tmp = r1;
                      r1 = r2;
                      r2 = r_tmp;
                      is_xcmpl = false;
                    }

                  if (!fpu_lower_xcmpu (cc, &stream, r0, r1, r2, is_double, is_xcmpl))
                    GOTO_FAIL;
                }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
              else
                /* I8 should have already been lowered before */
                GOTO_FAIL;
              BREAK;

            case JIT_OP_SELECTEQ:
            case JIT_OP_SELECTNE:
            case JIT_OP_SELECTGTS:
            case JIT_OP_SELECTGES:
            case JIT_OP_SELECTLTS:
            case JIT_OP_SELECTLES:
            case JIT_OP_SELECTGTU:
            case JIT_OP_SELECTGEU:
            case JIT_OP_SELECTLTU:
            case JIT_OP_SELECTLEU:
              LOAD_4ARGS;
              if (!lower_select (cc, &stream,
                                 EQ + (insn->opcode - JIT_OP_SELECTEQ),
                                 r0, r1, r2, r3))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_LDSELF:
              LOAD_1ARG;
              CHECK_KIND (r0, JIT_REG_KIND_I4);
              {
                M_Opnd m;
                m_from_b_d (m, esp_reg, 16 + 4);
                mov_r_m (regs_I4[jit_reg_no (r0)], m);
              }
              BREAK;

            case JIT_OP_LDJITINFO:
              LOAD_1ARG;
              CHECK_KIND (r0, JIT_REG_KIND_I4);
              {
                M_Opnd m;
                m_from_b_d (m, esp_reg, 16 + 8);
                mov_r_m (regs_I4[jit_reg_no (r0)], m);
              }
              BREAK;

            case JIT_OP_LDI1:
              LOAD_3ARGS;
              LD_R_R_R (I4, 1, true);
              BREAK;

            case JIT_OP_LDU1:
              LOAD_3ARGS;
              LD_R_R_R (I4, 1, false);
              BREAK;

            case JIT_OP_LDI2:
              LOAD_3ARGS;
              LD_R_R_R (I4, 2, true);
              BREAK;

            case JIT_OP_LDU2:
              LOAD_3ARGS;
              LD_R_R_R (I4, 2, false);
              BREAK;

            case JIT_OP_LDI4:
            case JIT_OP_LDU4:
              LOAD_3ARGS;
              LD_R_R_R (I4, 4, false);
              BREAK;

#ifdef CODEGEN_ENABLE_FLOATING_POINT
            case JIT_OP_LDF4:
              LOAD_3ARGS;
              LD_R_R_R (F4, 4, false);
              BREAK;

            case JIT_OP_LDF8:
              LOAD_3ARGS;
              LD_R_R_R (F8, 8, false);
              BREAK;
#endif

            case JIT_OP_STI1:
              LOAD_3ARGS_NO_ASSIGN;
              ST_R_R_R (I4, int32, 1);
              BREAK;

            case JIT_OP_STI2:
              LOAD_3ARGS_NO_ASSIGN;
              ST_R_R_R (I4, int32, 2);
              BREAK;

            case JIT_OP_STI4:
              LOAD_3ARGS_NO_ASSIGN;
              ST_R_R_R (I4, int32, 4);
              BREAK;

#ifdef CODEGEN_ENABLE_FLOATING_POINT
            case JIT_OP_STF4:
              LOAD_3ARGS_NO_ASSIGN;
              ST_R_R_R (F4, float, 4);
              BREAK;

            case JIT_OP_STF8:
              LOAD_3ARGS_NO_ASSIGN;
              ST_R_R_R (F8, double, 8);
              BREAK;
#endif

            case JIT_OP_JMP:
              LOAD_1ARG;
              CHECK_KIND (r0, JIT_REG_KIND_L4);
              if ( !( is_last_insn &&
                      label_is_neighboring (cc, label_index, jit_reg_no (r0)) ) )
                JMP_TO_LABEL (stream_offset, jit_reg_no (r0), label_index);
              BREAK;

            case JIT_OP_BEQ:
            case JIT_OP_BNE:
            case JIT_OP_BGTS:
            case JIT_OP_BGES:
            case JIT_OP_BLTS:
            case JIT_OP_BLES:
            case JIT_OP_BGTU:
            case JIT_OP_BGEU:
            case JIT_OP_BLTU:
            case JIT_OP_BLEU:
              LOAD_3ARGS;
              if (!lower_branch (cc, &stream, stream_offset, label_index,
                                 EQ + (insn->opcode - JIT_OP_BEQ),
                                 r0, r1, r2, is_last_insn))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_TABLESWITCH:
              {
                JitOpndTableSwitch *opnd = jit_insn_opndts (insn);
                if (!lower_tableswitch (cc, &stream, stream_offset,
                                        label_index, opnd, is_last_insn))
                  GOTO_FAIL;
              }
              BREAK;

            case JIT_OP_LOOKUPSWITCH:
              {
                JitOpndLookupSwitch *opnd = jit_insn_opndls (insn);
                if (!lower_lookupswitch (cc, &stream, stream_offset,
                                         label_index, opnd, is_last_insn))
                  GOTO_FAIL;
              }
              BREAK;

            case JIT_OP_CALLNATIVE:
              if (!lower_callnative (cc, &stream, stream_offset,
                                     label_index, insn,
                                     (total_stream_size
                                      + cur_label_stream_size
                                      - (uint32)cache_list[cache_index])))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_CALLBC:
              if (!lower_callbc (cc, &stream, stream_offset,
                                 label_index, insn,
                                 (total_stream_size
                                  + cur_label_stream_size
                                  - (uint32)cache_list[cache_index])))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_RETURNBC:
              if (!lower_returnbc (cc, &stream, stream_offset,
                                   label_index, insn))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_LEAVE:
              if (!lower_leave (cc, &stream, stream_offset,
                                label_index, insn,
                                (total_stream_size
                                 + cur_label_stream_size
                                 - (uint32)cache_list[cache_index])))
                GOTO_FAIL;
              BREAK;

            case JIT_OP_LEAVEFROMCALLBC:
              {
                M_Opnd m;

                /* eax = info->last_return_type */
                m_from_b_d (m, esp_reg, 16 + 8);
                mov_r_m (reg_I4_free, m);
                m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 20);
                mov_r_m (eax, m);

                /* recover callee saved registers and ret */
                ENCODER_FILL_END ();
                BREAK;
              }

#ifdef BEIHAI_JIT_FOR_DALVIK
            case JIT_OP_CHKGC:
              if (!lower_checkgc(cc, &stream, stream_offset, label_index))
                GOTO_FAIL;
              BREAK;
#endif
            default:
              jit_set_error (JIT_ERROR_UNSUPPORTED_OP);
              GOTO_FAIL;
            }
#ifdef CODEGEN_DUMP_LOWER_RESULT
          dump_stream (stream_last, (int32)(stream - stream_last));
#endif
#ifdef CODEGEN_TRACE_EXEC_RESULT
          if (!(insn->opcode ==JIT_OP_JMP ||
                insn->opcode ==JIT_OP_TABLESWITCH ||
                insn->opcode ==JIT_OP_LEAVE ||
                (insn->opcode >= JIT_OP_BEQ && insn->opcode <= JIT_OP_BLEU)))
            DUMP_INSN(cc, insn);
#endif

          for (j = 0; j < 3; j++)
            {
              JitReg r = real_opnd_to_reg[j];
              unsigned rel;

              if (jit_reg_is_const (r) && jit_reg_kind (r) == JIT_REG_KIND_I4
                  && (rel = jit_cc_get_const_I4_rel (cc, r)))
                {
                  unsigned offset = (total_stream_size
                                     + cur_label_stream_size
                                     + (EncoderBase_curRealOpnd[j].pos
                                        - cache_list[cache_index]));
                  add_aot_reloc_record (EncoderBase_curRealOpnd[j].size,
                                        offset, rel);
                }
            }
        }

      cache_size[cache_index] = stream - cache_list[cache_index];
      cur_label_stream_size += cache_size[cache_index];

      stream_list[label_index].size = cur_label_stream_size;
      stream_list[label_index].stream = jit_malloc (cur_label_stream_size);
      if (!stream_list[label_index].stream)
        GOTO_FAIL;

      stream = stream_list[label_index].stream;
      for (j = 0; j <= cache_index; j++)
        {
          memcpy (stream, cache_list[j], cache_size[j]);
          stream += cache_size[j];
        }

      total_stream_size += cur_label_stream_size;
    }

  if (jit_globals.options.aot_gen_mode)
    {
      if (cur_aot_reloc_record_index == AOT_RELOC_RECORD_NUM)
        jit_print_log ("V2.JIT: too many relocation records\n");
      else
        {
          unsigned size = sizeof (AotRelocRecord) * cur_aot_reloc_record_index;
          reloc_info = jit_malloc (size + 4);
          *(uint32 *)reloc_info = size;
          memcpy ((uint32 *)reloc_info + 1, aot_reloc_records, size);
        }
    }

  if (!(stream = jit_code_cache_alloc_for_region
        (total_stream_size, reloc_info, cc->method, cc->entry_bcip)))
    GOTO_FAIL;

  reloc_info = NULL;
  cc->jited_addr_begin = stream;
  cc->jited_addr_end = stream + total_stream_size;

  for (i = 0; i < label_num; i++ )
    {
      if (i > 0 && i < label_num - 1)
        label_index = i + 1;
      else if (i == 0)
        label_index = 0;
      else
        label_index = 1;

      jited_addr = jit_annl_jited_addr (cc, jit_reg_new (JIT_REG_KIND_L4,
                                                         label_index));
      memcpy (stream, stream_list[label_index].stream,
              stream_list[label_index].size);
      *jited_addr = stream;
      stream += stream_list[label_index].size;
    }

  replace_jmp_addr_from_virtual_to_absolute (cc);

#ifdef CODEGEN_DUMP_LOWER_RESULT
  /* This is to dump the Final lower result after jmp has been replaced, only enable if necessary */
  if (false) {
    dump_stream (cc->jited_addr_begin, (unsigned)stream - (unsigned)cc->jited_addr_begin);
  }
#endif

  jit_assert (check_aot_reloc_records ((uint8 *)cc->jited_addr_begin,
                                       cc->method));
  goto cleanup;

fail:
  return_value = false;

cleanup:
  /* Free the jmp info list */
  free_jmp_info_list ();
  for (label_index = 0; label_index < label_num; label_index ++)
    if (stream_list[label_index].stream)
      jit_free (stream_list[label_index].stream);
  jit_free (stream_list);

  for (j = MAX_STATIC_CACHE_NUM; j < cache_num; j ++)
    jit_free (cache_list[j]);
  if (reloc_info != NULL) {
    jit_free (reloc_info);
  }

#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf("\n");
  jit_printf(NULL);
#endif
  return return_value;
}

/**
 * Part of lower int64 to int32
 */

/* Create a new I4 register */
#define NEW_REG_I4(r)               \
  do {                              \
    r = jit_cc_new_reg_I4 (cc);     \
  } while (0)

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
_gen_insn (JitCompContext *cc, JitInsn *insn, JitInsn *new_insn,
           bool before)
{
  if (new_insn)
    {
      if (before)
        jit_insn_insert_before (insn, new_insn);
      else
        jit_insn_insert_after (insn, new_insn);
    }

  return new_insn;
}

/* Generate an instruction insert before insn. */
#define GEN_INSN(...)                           \
  _gen_insn (cc, insn, jit_cc_new_insn (cc, __VA_ARGS__), true)

/* Generate an instruction insert before insn. */
#define GEN_INSN_AFTER(...)                      \
  _gen_insn (cc, insn, jit_cc_new_insn (cc, __VA_ARGS__), false)

/* Remove current insn */
#define DEL_INSN(insn)                          \
  do {                                          \
    JitInsn *insn_prev = insn->prev;            \
                                                \
    jit_insn_unlink (insn);                     \
    insn = insn_prev;                           \
  } while (0)

/* Create a new const variable */
#define NEW_CONST(Type, val)                    \
  jit_cc_new_const_##Type (cc, val)

/* Create new I4 const */
#define CONST_I4(val)   NEW_CONST (I4, val)

/* Convert function pointer to intrinsic */
#define POINTER_TO_CONST(p)  NEW_CG_INTRINSIC(p)

/* Map I8 register to two I4 registers */
typedef struct I8toI4MapInfo
{
  JitReg i4_reg_0;
  JitReg i4_reg_1;
  /* Has already been maped or not */
  bool has_value;
} I8toI4MapInfo;

/**
 * Get I8 register's map info: get its two maped I4 registers
 *
 * @param cc the compiler context
 * @param map_table the I8 to I4 map table to search
 * @param i8_reg the original I8 register
 * @param i4_reg_0 return the first maped I4 register
 * @param i4_reg_1 return the second maped I4 register
 */
static void
get_map_info (JitCompContext *cc, I8toI4MapInfo *map_table,
              JitReg i8_reg, JitReg *i4_reg_0, JitReg *i4_reg_1)
{
  if (!jit_reg_is_const (i8_reg))
    {
      uint32 i8_reg_no = jit_reg_no (i8_reg);

      if (!map_table[i8_reg_no].has_value)
        {
          *i4_reg_0 = jit_cc_new_reg_I4 (cc);
          *i4_reg_1 = jit_cc_new_reg_I4 (cc);
          map_table[i8_reg_no].i4_reg_0 = *i4_reg_0;
          map_table[i8_reg_no].i4_reg_1 = *i4_reg_1;
          map_table[i8_reg_no].has_value = true;
          return;
        }

      *i4_reg_0 = map_table[i8_reg_no].i4_reg_0;
      *i4_reg_1 = map_table[i8_reg_no].i4_reg_1;
    }
  else
    {
      int64 i8_const_val = jit_cc_get_const_I8 (cc, i8_reg);
      int32 i4_const_val;

      memcpy (&i4_const_val, (char*)&i8_const_val, 4);
      *i4_reg_0 = jit_cc_new_const_I4 (cc, i4_const_val);
      memcpy (&i4_const_val, (char*)&i8_const_val + 4, 4);
      *i4_reg_1 = jit_cc_new_const_I4 (cc, i4_const_val);
    }
}

#define MAP_I8_TO_I4(i8_reg, i4_reg_0, i4_reg_1)        \
  get_map_info (cc, map_table, i8_reg, &i4_reg_0, &i4_reg_1)

#define ST_I8_TO_BUF(i4_r0, i4_r1, buf, offset)         \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (STI4, i4_r0, _r, CONST_I4 (offset));      \
    GEN_INSN (STI4, i4_r1, _r, CONST_I4 (offset + 4));  \
  } while (0)

#define LD_I8_FROM_BUF(i4_r0, i4_r1, buf, offset)       \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (LDI4, i4_r0, _r, CONST_I4 (offset));      \
    GEN_INSN (LDI4, i4_r1, _r, CONST_I4 (offset + 4));  \
  } while (0)

#define ST_I4_TO_BUF(i4_r, buf, offset)                 \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (STI4, i4_r, _r, CONST_I4 (offset));       \
  } while (0)

#define LD_I4_FROM_BUF(i4_r, buf, offset)               \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (LDI4, i4_r, _r, CONST_I4 (offset));       \
  } while (0)

#ifdef CODEGEN_ENABLE_FLOATING_POINT
#define ST_F4_TO_BUF(f4_r, buf, offset)                 \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (STF4, f4_r, _r, CONST_I4 (offset));       \
  } while (0)

#define LD_F4_FROM_BUF(f4_r, buf, offset)               \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (LDF4, f4_r, _r, CONST_I4 (offset));       \
 } while (0)

#define ST_F8_TO_BUF(f8_r, buf, offset)                 \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (STF8, f8_r, _r, CONST_I4 (offset));       \
  } while (0)

#define LD_F8_FROM_BUF(f8_r, buf, offset)               \
  do {                                                  \
    JitReg _r = CONST_I4 ((int32)buf);                  \
    GEN_INSN (LDF8, f8_r, _r, CONST_I4 (offset));       \
  } while (0)
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

#define GEN_INT64_INSN_OP1(func)                                    \
  do {                                                              \
    NEW_REG_I4 (r3);                                                \
    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);                                \
    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);                                \
    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);                                \
                                                                    \
    GEN_INSN (ADD, r3, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));  \
    GEN_INSN (STI4, i4_r2, r3, CONST_I4 (0));                       \
    GEN_INSN (STI4, i4_r3, r3, CONST_I4 (4));                       \
    GEN_INSN (STI4, i4_r4, r3, CONST_I4 (8));                       \
    GEN_INSN (STI4, i4_r5, r3, CONST_I4 (12));                      \
    if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,                        \
                        POINTER_TO_CONST (jit_int64_##func), 1))) {     \
      *(jit_insn_opndv (insn_tmp, 2)) = r3;                         \
    }                                                               \
    GEN_INSN (LDI4, i4_r0, r3, CONST_I4 (0));                       \
    GEN_INSN (LDI4, i4_r1, r3, CONST_I4 (4));                       \
    DEL_INSN (insn);                                                \
  } while (0)

#define GEN_INT64_INSN_OP2(func)                                    \
  do {                                                              \
    NEW_REG_I4 (r3);                                                \
    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);                                \
    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);                                \
                                                                    \
    GEN_INSN (ADD, r3, cc->self_reg,                                \
              CONST_I4 (JIT_CACHE_OFFSET));              \
    GEN_INSN (STI4, i4_r2, r3, CONST_I4 (0));                       \
    GEN_INSN (STI4, i4_r3, r3, CONST_I4 (4));                       \
    GEN_INSN (STI4, r2, r3, CONST_I4 (8));                          \
    if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,                        \
                        POINTER_TO_CONST (jit_int64_##func), 1))) {     \
      *(jit_insn_opndv (insn_tmp, 2)) = r3;                         \
    }                                                               \
    GEN_INSN (LDI4, i4_r0, r3, CONST_I4 (0));                       \
    GEN_INSN (LDI4, i4_r1, r3, CONST_I4 (4));                       \
    DEL_INSN (insn);                                                \
  } while (0)

#define GEN_NO_CHECK_BRANCH_INSN(op)                                \
    do {                                                            \
      LOAD_3ARGS;                                                   \
      if (jit_reg_kind (r0) == JIT_REG_KIND_I8)                     \
        {                                                           \
          CHECK_KIND (r1, JIT_REG_KIND_L4);                         \
          CHECK_KIND (r2, JIT_REG_KIND_L4);                         \
                                                                    \
          MAP_I8_TO_I4 (r0, i4_r0, i4_r1);                          \
                                                                    \
          GEN_INSN (op, i4_r0, r1, r2);                             \
          DEL_INSN (insn);                                          \
        }                                                           \
    } while (0)

#define GEN_CHECK_BRANCH_INSN(op)                                   \
  do {                                                              \
    LOAD_3ARGS;                                                     \
    if (jit_reg_kind (r0) == JIT_REG_KIND_I8)                       \
      {                                                             \
        CHECK_KIND (r1, JIT_REG_KIND_L4);                           \
        CHECK_KIND (r2, JIT_REG_KIND_L4);                           \
                                                                    \
        NEW_REG_I4 (r3);                                            \
        NEW_REG_I4 (r4);                                            \
        MAP_I8_TO_I4 (r0, i4_r0, i4_r1);                            \
                                                                    \
        GEN_INSN (CMP, cc->cmp_reg, i4_r0, CONST_I4 (0));           \
        GEN_INSN (SELECTNE, r3, cc->cmp_reg,                        \
                  CONST_I4 (1), CONST_I4 (0));                      \
        GEN_INSN (CMP, cc->cmp_reg, i4_r1, CONST_I4 (0));           \
        GEN_INSN (SELECTNE, r4, cc->cmp_reg, r4, r3);               \
        GEN_INSN (op, r4, r1, r2);                                  \
        DEL_INSN (insn);                                            \
      }                                                             \
  } while (0)

#define GEN_SELECT_INSN(op)                                         \
  do {                                                              \
    LOAD_4ARGS;                                                     \
    if (jit_reg_kind (r0) == JIT_REG_KIND_I8)                       \
      {                                                             \
        CHECK_KIND (r1, JIT_REG_KIND_I4);                           \
        CHECK_KIND (r2, JIT_REG_KIND_I8);                           \
        CHECK_KIND (r3, JIT_REG_KIND_I8);                           \
                                                                    \
        MAP_I8_TO_I4 (r0, i4_r0, i4_r1);                            \
        MAP_I8_TO_I4 (r2, i4_r2, i4_r3);                            \
        MAP_I8_TO_I4 (r3, i4_r4, i4_r5);                            \
                                                                    \
        GEN_INSN (op, r1, i4_r0, i4_r2, i4_r4);                     \
        GEN_INSN (op, r1, i4_r1, i4_r3, i4_r5);                     \
      }                                                             \
  } while (0)

static uint8 hreg_info_F4[3][7];
static uint8 hreg_info_F8[3][7];

bool
jit_codegen_x86_lower (JitCompContext *cc)
{
  int32 label_index, end_label_index;
  JitBlock *block;
  JitInsn *insn, *insn_tmp;
  I8toI4MapInfo *map_table;
  JitReg r0, r1, r2, r3, r4;
  JitReg i4_r0, i4_r1, i4_r2, i4_r3, i4_r4, i4_r5;
  JitReg eax_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_EAX_INDEX);
  JitReg ecx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_ECX_INDEX);
  JitReg edx_hreg = jit_reg_new (JIT_REG_KIND_I4, REG_EDX_INDEX);
#ifdef CODEGEN_ENABLE_FLOATING_POINT
  JitReg f0_hreg = jit_reg_new (JIT_REG_KIND_F4, 0);
  JitReg d0_hreg = jit_reg_new (JIT_REG_KIND_F8, 0);
#endif
  uint32 reg_num_f4 = jit_cc_reg_num (cc, JIT_REG_KIND_F4);
  uint32 reg_num_f8 = jit_cc_reg_num (cc, JIT_REG_KIND_F8);

  reg_num_f4 -= jit_cc_hreg_num (cc, JIT_REG_KIND_F4);
  reg_num_f8 -= jit_cc_hreg_num (cc, JIT_REG_KIND_F8);

#ifndef CODEGEN_ENABLE_FLOATING_POINT
  if (reg_num_f4 > 0 || reg_num_f8 > 0)
    {
      jit_set_error (JIT_ERROR_UNSUPPORTED_OP);
      return false;
    }
#else
  if (reg_num_f4 > 0 && reg_num_f8 == 0)
    {
      memset (hreg_info_F4[0], 0, 7);
      /*can_use_f4_st0 = true;*/
    }
  else if (reg_num_f8 > 0 && reg_num_f4 == 0)
    {
      memset (hreg_info_F8[0], 0, 7);
      /*can_use_f8_st0 = true;*/
    }
  else if (reg_num_f4 > 0 && reg_num_f8 > 0)
    {
      const uint8 reg_fixed1[7] = {0, 0, 0, 0, 1, 1, 1};
      const uint8 reg_fixed2[7] = {1, 1, 1, 1, 0, 0, 0};
      if (reg_num_f4 >= reg_num_f8)
        {
          memcpy (hreg_info_F4[0], reg_fixed1, 7);
          memcpy (hreg_info_F8[0], reg_fixed2, 7);
          /*can_use_f4_st0 = true;*/
        }
      else
        {
          memcpy (hreg_info_F8[0], reg_fixed1, 7);
          memcpy (hreg_info_F4[0], reg_fixed2, 7);
          /*can_use_f8_st0 = true;*/
        }
    }
#endif

  map_table  = jit_malloc (sizeof (I8toI4MapInfo) *
                           jit_cc_reg_num (cc, JIT_REG_KIND_I8));
  if (!map_table)
    return false;

  memset (map_table, 0, sizeof (I8toI4MapInfo) *
                        jit_cc_reg_num (cc, JIT_REG_KIND_I8));

  JIT_FOREACH_BLOCK (cc, label_index, end_label_index, block)
    {
      JIT_FOREACH_INSN (block, insn)
        {
          switch (insn->opcode)
            {
              case JIT_OP_MOV:
                LOAD_2ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);

                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);

                    GEN_INSN (MOV, i4_r0, i4_r2);
                    GEN_INSN (MOV, i4_r1, i4_r3);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_I4TOI8:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_I4);

                NEW_REG_I4 (r2);
                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (MOV, i4_r0, r1);
                GEN_INSN (CMP, cc->cmp_reg, r1, CONST_I4(0));
                GEN_INSN (SELECTLTS, i4_r1, cc->cmp_reg, CONST_I4(-1), CONST_I4(0));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_U4TOI8:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_I4);

                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (MOV, i4_r0, r1);
                GEN_INSN (MOV, i4_r1, CONST_I4 (0));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_I8TOI4:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I4);
                CHECK_KIND (r1, JIT_REG_KIND_I8);

                MAP_I8_TO_I4 (r1, i4_r0, i4_r1);

                GEN_INSN (MOV, r0, i4_r0);
                DEL_INSN (insn);
                BREAK;

#ifdef CODEGEN_ENABLE_FLOATING_POINT
              case JIT_OP_I8TOF4:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_F4);
                CHECK_KIND (r1, JIT_REG_KIND_I8);

                NEW_REG_I4 (r2);
                MAP_I8_TO_I4 (r1, i4_r2, i4_r3);

                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STI4, i4_r2, r2, CONST_I4 (0));
                GEN_INSN (STI4, i4_r3, r2, CONST_I4 (4));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,
                                    POINTER_TO_CONST (jit_int64_to_float), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                GEN_INSN (LDF4, r0, r2, CONST_I4 (0));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_I8TOF8:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_F8);
                CHECK_KIND (r1, JIT_REG_KIND_I8);

                NEW_REG_I4 (r2);
                MAP_I8_TO_I4 (r1, i4_r2, i4_r3);

                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STI4, i4_r2, r2, CONST_I4 (0));
                GEN_INSN (STI4, i4_r3, r2, CONST_I4 (4));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,
                                    POINTER_TO_CONST (jit_int64_to_double), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                GEN_INSN (LDF8, r0, r2, CONST_I4 (0));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_F4TOI8:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_F4);

                NEW_REG_I4 (r2);
                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STF4, r1, r2, CONST_I4 (0));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,
                                    POINTER_TO_CONST (jit_int64_from_float), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                GEN_INSN (LDI4, i4_r0, r2, CONST_I4 (0));
                GEN_INSN (LDI4, i4_r1, r2, CONST_I4 (4));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_F4TOI4:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I4);
                CHECK_KIND (r1, JIT_REG_KIND_F4);

                NEW_REG_I4 (r2);
                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STF4, r1, r2, CONST_I4 (0));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, r0,
                                    POINTER_TO_CONST (jit_int32_from_float), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_F8TOI8:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_F8);

                NEW_REG_I4 (r2);
                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STF8, r1, r2, CONST_I4 (0));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, 0, 
                                    POINTER_TO_CONST (jit_int64_from_double), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                GEN_INSN (LDI4, i4_r0, r2, CONST_I4 (0));
                GEN_INSN (LDI4, i4_r1, r2, CONST_I4 (4));
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_F8TOI4:
                LOAD_2ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I4);
                CHECK_KIND (r1, JIT_REG_KIND_F8);

                NEW_REG_I4 (r2);
                GEN_INSN (ADD, r2, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                GEN_INSN (STF8, r1, r2, CONST_I4 (0));
                if ((insn_tmp = GEN_INSN (CALLNATIVE, r0,
                                    POINTER_TO_CONST (jit_int32_from_double), 1)))
                  *(jit_insn_opndv (insn_tmp, 2)) = r2;
                DEL_INSN (insn);
                BREAK;
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */

              case JIT_OP_LDI8:
              case JIT_OP_LDU8:
                LOAD_3ARGS;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_I4);
                CHECK_KIND (r2, JIT_REG_KIND_I4);

                NEW_REG_I4 (r3);
                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (LDI4, i4_r0, r1, r2);
                if (!jit_reg_is_const (r2))
                  {
                    GEN_INSN (ADD, r3, r2, CONST_I4 (4));
                    GEN_INSN (LDI4, i4_r1, r1, r3);
                  }
                else
                  {
                    int32 data = jit_cc_get_const_I4 (cc, r2);
                    data += 4;
                    GEN_INSN (LDI4, i4_r1, r1, CONST_I4 (data));
                  }
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_STI8:
                LOAD_3ARGS_NO_ASSIGN;
                CHECK_KIND (r0, JIT_REG_KIND_I8);
                CHECK_KIND (r1, JIT_REG_KIND_I4);
                CHECK_KIND (r2, JIT_REG_KIND_I4);

                NEW_REG_I4 (r3);
                MAP_I8_TO_I4 (r0, i4_r0, i4_r1);

                GEN_INSN (STI4, i4_r0, r1, r2);
                if (!jit_reg_is_const (r2))
                  {
                    GEN_INSN (ADD, r3, r2, CONST_I4 (4));
                    GEN_INSN (STI4, i4_r1, r1, r3);
                  }
                else
                  {
                    int32 data = jit_cc_get_const_I4 (cc, r2);
                    data += 4;
                    GEN_INSN (STI4, i4_r1, r1, CONST_I4 (data));
                  }
                DEL_INSN (insn);
                BREAK;

              case JIT_OP_NEG:
                LOAD_2ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);

                    NEW_REG_I4 (r2);
                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);

                    GEN_INSN (CMP, cc->cmp_reg, i4_r2, CONST_I4 (0));
                    GEN_INSN (SELECTEQ, r2, cc->cmp_reg,
                                CONST_I4 (0), CONST_I4 (1));
                    GEN_INSN (NEG, i4_r0, i4_r2);
                    GEN_INSN (ADD, i4_r1, i4_r3, r2);
                    GEN_INSN (NEG, i4_r1, i4_r1);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_ADD:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    NEW_REG_I4 (r3);
                    NEW_REG_I4 (r4);
                    /* use i4_r0, i4_r1 to save result temporarily */
                    NEW_REG_I4 (i4_r0);
                    NEW_REG_I4 (i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    GEN_INSN (ADD, i4_r0, i4_r2, i4_r4);
                    GEN_INSN (ADD, i4_r1, i4_r3, i4_r5);
                    /* calculate the carry and add the carry */
                    GEN_INSN (CMP, cc->cmp_reg, i4_r2, i4_r0);
                    GEN_INSN (SELECTGTU, r3, cc->cmp_reg, CONST_I4 (1), CONST_I4 (0));
                    GEN_INSN (ADD, i4_r1, i4_r1, r3);

                    /* save temp result to actual result */
                    MAP_I8_TO_I4 (r0, i4_r2, i4_r3);
                    GEN_INSN (MOV, i4_r2, i4_r0);
                    GEN_INSN (MOV, i4_r3, i4_r1);

                    DEL_INSN (insn);
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4 ||
                         jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    CHECK_EQKIND (r0, r1);
                    CHECK_EQKIND (r0, r2);

                    if (r0 != r1 && r0 != r2)
                      {
                        GEN_INSN (MOV, r0, r1);
                        GEN_INSN (ADD, r0, r0, r2);
                        DEL_INSN (insn);
                      }
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_SUB:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    NEW_REG_I4 (r3);
                    NEW_REG_I4 (r4);
                    /* use i4_r0, i4_r1 to save result temporarily */
                    NEW_REG_I4 (i4_r0);
                    NEW_REG_I4 (i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    GEN_INSN (SUB, i4_r0, i4_r2, i4_r4);
                    GEN_INSN (SUB, i4_r1, i4_r3, i4_r5);
                    /* calculate the carry and sub the carry */
                    GEN_INSN (CMP, cc->cmp_reg, i4_r0, i4_r2);
                    GEN_INSN (SELECTGTU, r3, cc->cmp_reg, CONST_I4 (1), CONST_I4 (0));
                    GEN_INSN (SUB, i4_r1, i4_r1, r3);

                    /* save temp result to actual result */
                    MAP_I8_TO_I4 (r0, i4_r2, i4_r3);
                    GEN_INSN (MOV, i4_r2, i4_r0);
                    GEN_INSN (MOV, i4_r3, i4_r1);

                    DEL_INSN (insn);
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4 ||
                         jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    CHECK_EQKIND (r0, r1);
                    CHECK_EQKIND (r0, r2);

                    if (r0 != r1 && r0 != r2)
                      {
                        GEN_INSN (MOV, r0, r1);
                        GEN_INSN (SUB, r0, r0, r2);
                        DEL_INSN (insn);
                      }
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_MUL:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    GEN_INT64_INSN_OP1 (mul);
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4 ||
                         jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    CHECK_EQKIND (r0, r1);
                    CHECK_EQKIND (r0, r2);

                    if (r0 != r1 && r0 != r2)
                      {
                        GEN_INSN (MOV, r0, r1);
                        GEN_INSN (MUL, r0, r0, r2);
                        DEL_INSN (insn);
                      }
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_DIV:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    GEN_INT64_INSN_OP1 (div);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4)
                  {
                    if (jit_reg_is_const (r2) &&
                        jit_cc_get_const_I4 (cc, r2) == 1)
                      {
                        /* a / 1 = a */
                        GEN_INSN (MOV, r0, r1);
                        DEL_INSN (insn);
                      }
                    else if (jit_reg_is_const (r2) &&
                        jit_cc_get_const_I4 (cc, r2) == -1)
                      {
                        /* a / -1 = -a */
                        GEN_INSN (NEG, r0, r1);
                        DEL_INSN (insn);
                      }
                    else if (jit_reg_is_const (r1) &&
                             jit_reg_is_const (r2) &&
                             jit_cc_get_const_I4 (cc, r2) != 0)
                      {
                        /* calcualte the div result of two consts */
                        int32 div_result = jit_cc_get_const_I4 (cc, r1) /
                                            jit_cc_get_const_I4 (cc, r2);
                        GEN_INSN (MOV, r0, CONST_I4 (div_result));
                        DEL_INSN (insn);
                      }
                    else
                      {
                        /* Enforce register supporting byte operation.  */

                        /* Replace insn to DIV eax, eax, r2 */
                        GEN_INSN (MOV, eax_hreg, r1);
                        if (!jit_reg_is_const (r2))
                          {
                            GEN_INSN (MOV, ecx_hreg, r2);
                            GEN_INSN (DIV, eax_hreg, eax_hreg, ecx_hreg);
                          }
                        else
                          GEN_INSN (DIV, eax_hreg, eax_hreg, r2);

                        /* Save Result */
                        GEN_INSN (MOV, r0, eax_hreg);

                        /**
                         * Just to indicate that edx is used,
                         * register allocator cannot spill it out
                         */
                        GEN_INSN (MOV, edx_hreg, edx_hreg);

                        DEL_INSN (insn);
                      }
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4 ||
                         jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    CHECK_EQKIND (r0, r1);
                    CHECK_EQKIND (r0, r2);

                    if (r0 != r1 && r0 != r2)
                      {
                        GEN_INSN (MOV, r0, r1);
                        GEN_INSN (DIV, r0, r0, r2);
                        DEL_INSN (insn);
                      }
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_REM:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    GEN_INT64_INSN_OP1 (rem);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4)
                  {
                    if (jit_reg_is_const (r2) &&
                        (jit_cc_get_const_I4 (cc, r2) == 1 ||
                         jit_cc_get_const_I4 (cc, r2) == -1))
                      {
                        /* a % 1 = 0 and a % -1 = 0 */
                        GEN_INSN (MOV, r0, CONST_I4 (0));
                        DEL_INSN (insn);
                      }
                    else if (jit_reg_is_const (r1) &&
                             jit_reg_is_const (r2) &&
                             jit_cc_get_const_I4 (cc, r2) != 0)
                      {
                        /* calcualte the rem result of two consts */
                        int32 rem_result = jit_cc_get_const_I4 (cc, r1) %
                                            jit_cc_get_const_I4 (cc, r2);
                        GEN_INSN (MOV, r0, CONST_I4 (rem_result));
                        DEL_INSN (insn);
                      }
                    else
                      {
                        /* Enforce register supporting byte operation.  */

                        /* Replace insn to REM edx, eax, r2 */
                        GEN_INSN (MOV, eax_hreg, r1);
                        if (!jit_reg_is_const (r2))
                          {
                            GEN_INSN (MOV, ecx_hreg, r2);
                            GEN_INSN (REM, edx_hreg, eax_hreg, ecx_hreg);
                          }
                        else
                          GEN_INSN (REM, edx_hreg, eax_hreg, r2);

                        /* Save Result */
                        GEN_INSN (MOV, r0, edx_hreg);

                        DEL_INSN (insn);
                      }
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_F4);
                    CHECK_KIND (r2, JIT_REG_KIND_F4);

                    NEW_REG_I4 (r3);
                    GEN_INSN (ADD, r3, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                    GEN_INSN (STF4, r1, r3, CONST_I4 (0));
                    GEN_INSN (STF4, r2, r3, CONST_I4 (4));
                    if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,
                                              POINTER_TO_CONST (jit_float_rem), 1)))
                      *(jit_insn_opndv (insn_tmp, 2)) = r3;
                    GEN_INSN (LDF4, r0, r3, CONST_I4 (0));
                    DEL_INSN (insn);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_F8);
                    CHECK_KIND (r2, JIT_REG_KIND_F8);

                    NEW_REG_I4 (r3);
                    GEN_INSN (ADD, r3, cc->self_reg, CONST_I4 (JIT_CACHE_OFFSET));
                    GEN_INSN (STF8, r1, r3, CONST_I4 (0));
                    GEN_INSN (STF8, r2, r3, CONST_I4 (8));
                    if ((insn_tmp = GEN_INSN (CALLNATIVE, 0,
                                              POINTER_TO_CONST (jit_double_rem), 1)))
                      *(jit_insn_opndv (insn_tmp, 2)) = r3;
                    GEN_INSN (LDF8, r0, r3, CONST_I4 (0));
                    DEL_INSN (insn);
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_SHL:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    GEN_INT64_INSN_OP2 (shl);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4 &&
                         !jit_reg_is_const (r2))
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I4);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    /* Enforce register supporting byte operation. */
                    GEN_INSN (MOV, eax_hreg, r1);
                    GEN_INSN (MOV, ecx_hreg, r2);
                    GEN_INSN (SHL, eax_hreg, eax_hreg, ecx_hreg);
                    GEN_INSN (MOV, r0, eax_hreg);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_SHRS:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    GEN_INT64_INSN_OP2 (shrs);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4 &&
                         !jit_reg_is_const (r2))
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I4);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    /* Enforce register supporting byte operation. */
                    GEN_INSN (MOV, eax_hreg, r1);
                    GEN_INSN (MOV, ecx_hreg, r2);
                    GEN_INSN (SHRS, eax_hreg, eax_hreg, ecx_hreg);
                    GEN_INSN (MOV, r0, eax_hreg);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_SHRU:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    GEN_INT64_INSN_OP2 (shru);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4 &&
                         !jit_reg_is_const (r2))
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I4);
                    CHECK_KIND (r2, JIT_REG_KIND_I4);

                    /* Enforce register supporting byte operation. */
                    GEN_INSN (MOV, eax_hreg, r1);
                    GEN_INSN (MOV, ecx_hreg, r2);
                    GEN_INSN (SHRU, eax_hreg, eax_hreg, ecx_hreg);
                    GEN_INSN (MOV, r0, eax_hreg);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_OR:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    GEN_INSN (OR, i4_r0, i4_r2, i4_r4);
                    GEN_INSN (OR, i4_r1, i4_r3, i4_r5);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_XOR:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    GEN_INSN (XOR, i4_r0, i4_r2, i4_r4);
                    GEN_INSN (XOR, i4_r1, i4_r3, i4_r5);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_AND:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    GEN_INSN (AND, i4_r0, i4_r2, i4_r4);
                    GEN_INSN (AND, i4_r1, i4_r3, i4_r5);
                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_CMP:
                LOAD_3ARGS;
                if (jit_reg_kind (r1) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    NEW_REG_I4 (r3);
                    NEW_REG_I4 (r4);
                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    /* calculate the compare result of low 4 bytes */
                    GEN_INSN (XCMPLU, r4, i4_r2, i4_r4);

                    /* calculate the compare result of high 4 bytes */
                    GEN_INSN (XCMPLS, r3, i4_r3, i4_r5);

                    /**
                     * high 4 bytes not equal, return compare result of
                     * high 4 bytes, else return compare result of low 4 bytes
                     */
                    GEN_INSN (CMP, cc->cmp_reg, r3, CONST_I4 (0));
                    GEN_INSN (SELECTNE, r3, cc->cmp_reg, r3, r4);
                    GEN_INSN (CMP, cc->cmp_reg, r3, CONST_I4 (0));

                    DEL_INSN (insn);
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r1) == JIT_REG_KIND_F4 ||
                         jit_reg_kind (r1) == JIT_REG_KIND_F8)
                  {
                    GEN_INSN (MOV, eax_hreg, eax_hreg);
                  }
#endif
                BREAK;

              case JIT_OP_XCMPLS:
              case JIT_OP_XCMPLU:
              case JIT_OP_XCMPGS:
              case JIT_OP_XCMPGU:
                LOAD_3ARGS;
                if (jit_reg_kind (r1) == JIT_REG_KIND_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    CHECK_KIND (r2, JIT_REG_KIND_I8);

                    NEW_REG_I4 (r3);
                    NEW_REG_I4 (r4);

                    MAP_I8_TO_I4 (r1, i4_r2, i4_r3);
                    MAP_I8_TO_I4 (r2, i4_r4, i4_r5);

                    /* calculate the compare result of low 4 bytes */
                    GEN_INSN (XCMPLU, r4, i4_r2, i4_r4);

                    /* calculate the compare result of high 4 bytes */
                    GEN_INSN (XCMPLS, r3, i4_r3, i4_r5);

                    /**
                     * high 4 bytes not equal, return compare result of
                     * high 4 bytes, else return compare result of low 4 bytes
                     */
                    GEN_INSN (CMP, cc->cmp_reg, r3, CONST_I4 (0));
                    GEN_INSN (SELECTNE, r0, cc->cmp_reg, r3, r4);

                    DEL_INSN (insn);
                  }
                BREAK;

              case JIT_OP_BEQ:
                GEN_NO_CHECK_BRANCH_INSN (BEQ);
                BREAK;

              case JIT_OP_BNE:
                GEN_NO_CHECK_BRANCH_INSN (BNE);
                BREAK;

              case JIT_OP_BGTU:
                GEN_NO_CHECK_BRANCH_INSN (BGTU);
                BREAK;

              case JIT_OP_BGEU:
                GEN_NO_CHECK_BRANCH_INSN (BGEU);
                BREAK;

              case JIT_OP_BLTU:
                GEN_NO_CHECK_BRANCH_INSN (BLTU);
                BREAK;

              case JIT_OP_BLEU:
                GEN_NO_CHECK_BRANCH_INSN (BLEU);
                BREAK;

              case JIT_OP_BGTS:
                GEN_CHECK_BRANCH_INSN (BGTS);
                BREAK;

              case JIT_OP_BGES:
                GEN_CHECK_BRANCH_INSN (BGES);
                BREAK;

              case JIT_OP_BLTS:
                GEN_CHECK_BRANCH_INSN (BLTS);
                BREAK;

              case JIT_OP_BLES:
                GEN_CHECK_BRANCH_INSN (BLES);
                BREAK;

              case JIT_OP_SELECTEQ:
                GEN_SELECT_INSN (SELECTEQ);
                BREAK;

              case JIT_OP_SELECTNE:
                GEN_SELECT_INSN (SELECTNE);
                BREAK;

              case JIT_OP_SELECTGTS:
                GEN_SELECT_INSN (SELECTGTS);
                BREAK;

              case JIT_OP_SELECTGES:
                GEN_SELECT_INSN (SELECTGES);
                BREAK;

              case JIT_OP_SELECTLTS:
                GEN_SELECT_INSN (SELECTLTS);
                BREAK;

              case JIT_OP_SELECTLES:
                GEN_SELECT_INSN (SELECTLES);
                BREAK;

              case JIT_OP_SELECTGTU:
                GEN_SELECT_INSN (SELECTGTU);
                BREAK;

              case JIT_OP_SELECTGEU:
                GEN_SELECT_INSN (SELECTGEU);
                BREAK;

              case JIT_OP_SELECTLTU:
                GEN_SELECT_INSN (SELECTLTU);
                BREAK;

              case JIT_OP_SELECTLEU:
                GEN_SELECT_INSN (SELECTLEU);
                BREAK;

              case JIT_OP_STI1:
                if (!jit_reg_is_const (*jit_insn_opnd (insn, 0)))
                  {
                    /* Enforce register supporting byte operation. */
                    GEN_INSN (MOV, eax_hreg, *jit_insn_opnd (insn, 0));
                    *jit_insn_opnd (insn, 0) = eax_hreg;
                  }
                BREAK;

              case JIT_OP_I4TOI1:
              case JIT_OP_I4TOU1:
                if (!jit_reg_is_const (*jit_insn_opnd (insn, 1)))
                  {
                    /* Enforce register supporting byte operation. */
                    GEN_INSN (MOV, eax_hreg, *jit_insn_opnd (insn, 1));
                    *jit_insn_opnd (insn, 1) = eax_hreg;
                  }
                BREAK;

              case JIT_OP_CALLBC:
                LOAD_3ARGS;
                if (jit_reg_kind (r0) == JIT_REG_KIND_I8)
                  {
                    MAP_I8_TO_I4 (r0, i4_r0, i4_r1);
                    GEN_INSN (MOV, edx_hreg, edx_hreg);
                    /* eax reg may be overwritten by register allocator,
                       so protect it temporarily. TODO: fix bug in 
                       register allocator */
                    GEN_INSN (MOV, eax_hreg, eax_hreg);
                    *(jit_insn_opnd (insn, 0)) = ecx_hreg;
                    *(jit_insn_opnd (insn, 1)) = edx_hreg;
                    GEN_INSN_AFTER (MOV, i4_r1, edx_hreg);
                    GEN_INSN_AFTER (MOV, i4_r0, ecx_hreg);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_I4)
                  {
                    *(jit_insn_opnd (insn, 0)) = ecx_hreg;
                    GEN_INSN_AFTER (MOV, r0, ecx_hreg);
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F4)
                  {
                    *(jit_insn_opnd (insn, 0)) = f0_hreg;
                    GEN_INSN_AFTER (MOV, r0, f0_hreg);
                  }
                else if (jit_reg_kind (r0) == JIT_REG_KIND_F8)
                  {
                    *(jit_insn_opnd (insn, 0)) = d0_hreg;
                    GEN_INSN_AFTER (MOV, r0, d0_hreg);
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_RETURNBC:
                LOAD_3ARGS_NO_ASSIGN;
                if (jit_cc_get_const_I4 (cc, r0) == JIT_INTERP_ACTION_RET_I8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I8);
                    MAP_I8_TO_I4 (r1, i4_r0, i4_r1);
                    GEN_INSN (MOV, ecx_hreg, i4_r0);
                    GEN_INSN (MOV, edx_hreg, i4_r1);
                    *(jit_insn_opnd (insn, 1)) = ecx_hreg;
                    *(jit_insn_opnd (insn, 2)) = edx_hreg;
                  }
                else if (jit_cc_get_const_I4 (cc, r0) == JIT_INTERP_ACTION_RET_I4 ||
                         jit_cc_get_const_I4 (cc, r0) == JIT_INTERP_ACTION_RET_REF)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_I4);
                    GEN_INSN (MOV, ecx_hreg, r1);
                    *(jit_insn_opnd (insn, 1)) = ecx_hreg;
                  }
#ifdef CODEGEN_ENABLE_FLOATING_POINT
                else if (jit_cc_get_const_I4 (cc, r0) == JIT_INTERP_ACTION_RET_F4)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_F4);
                    GEN_INSN (MOV, f0_hreg, r1);
                    *(jit_insn_opnd (insn, 1)) = f0_hreg;
                  }
                else if (jit_cc_get_const_I4 (cc, r0) == JIT_INTERP_ACTION_RET_F8)
                  {
                    CHECK_KIND (r1, JIT_REG_KIND_F8);
                    GEN_INSN (MOV, d0_hreg, r1);
                    *(jit_insn_opnd (insn, 1)) = d0_hreg;
                  }
#endif /* end of CODEGEN_ENABLE_FLOATING_POINT */
                BREAK;

              case JIT_OP_CALLNATIVE:
                {
                  r0 = *(jit_insn_opndv (insn, 0));
                  if (jit_reg_kind (r0) == JIT_REG_KIND_I4)
                    {
                      GEN_INSN_AFTER (MOV, r0, eax_hreg);
                      *(jit_insn_opndv (insn, 0)) = eax_hreg;
                    }
                  BREAK;
                }

              default:
                BREAK;
            }
        }
    }

  jit_free (map_table);
  return true;

#ifdef CODEGEN_CHECK_ARGS
fail:

  jit_free (map_table);
  return false;
#endif
}

void
jit_codegen_x86_free_native (JitCompContext *cc)
{
  void **jited_addr;
  int32 label_index, label_num;

  /* free the whole native code block */
  if (cc->jited_addr_begin)
    jit_code_cache_free (cc->jited_addr_begin);
  cc->jited_addr_begin = NULL;
  cc->jited_addr_end = NULL;

  label_num = jit_cc_label_num (cc);
  for (label_index = 0; label_index < label_num; label_index ++)
    {
      /* clear each label's jited address */
      jited_addr = jit_annl_jited_addr (cc,
                            jit_reg_new(JIT_REG_KIND_L4, label_index));

      *jited_addr = NULL;
    }
}

void
jit_codegen_x86_dump_native (void *begin_addr, void *end_addr)
{
  if (begin_addr && end_addr && end_addr > begin_addr)
    {
      char buf[256];
      char *stream = begin_addr;

      jit_printf ("\n");
      while ( stream < (char*) end_addr)
        {
          jit_printf ("%08X:", (int32)stream);
          stream = decoder_disassemble_instr(stream, buf, sizeof (buf));
          jit_printf ("    %s\n", buf);
        }
      jit_printf ("\n");
    }
}

/* Init registers used by gen_native interface */
static void
regs_init ()
{
  R_Opnd_create(&regs_I4[REG_EBP_INDEX], ebp_reg);
  R_Opnd_create(&regs_I4[REG_EAX_INDEX], eax_reg);
  R_Opnd_create(&regs_I4[REG_EBX_INDEX], ebx_reg);
  R_Opnd_create(&regs_I4[REG_ECX_INDEX], ecx_reg);
  R_Opnd_create(&regs_I4[REG_EDX_INDEX], edx_reg);
  R_Opnd_create(&regs_I4[REG_EDI_INDEX], edi_reg);
  R_Opnd_create(&regs_I4[REG_ESI_INDEX], esi_reg);
  R_Opnd_create(&reg_I4_free,
                R_Opnd_get_reg_no (&regs_I4[REG_I4_FREE_INDEX]));
}

/* Init begin code block */
static bool
code_block_init ()
{
  Imm_Opnd imm;
  M_Opnd m;
  char *stream, *stream_saved;
  code_block_switch_to_jited_from_interp =
                    jit_code_cache_alloc (MAX_CODE_BLOCK_SIZE, "interp_switch_jited");
  if (!code_block_switch_to_jited_from_interp)
    return false;

  stream = code_block_switch_to_jited_from_interp;
  /**
   * save_callee_saved_registers, fp_reg = info->frame,
   *and jump target
   */
  ENCODER_FILL_START ();
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("V1.Dump Lower for glues\n");
  jit_printf ("code_block_switch_to_jited_from_interp:\n");
  dump_stream (code_block_switch_to_jited_from_interp,
               (int32)(stream - code_block_switch_to_jited_from_interp));
#endif

  code_block_switch_to_interp_from_jited =
                    jit_code_cache_alloc (MAX_CODE_BLOCK_SIZE, "jited_switch_interp");
  if (!code_block_switch_to_interp_from_jited)
    goto free3;

  stream = code_block_switch_to_interp_from_jited;
  /* eax = JIT_INTERP_ACTION_NORMAL */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_NORMAL, true);
  mov_r_imm (eax, imm);
  stream_saved = stream;
  /* info->frame = fp_reg */
  m_from_b_d (m, esp_reg, 16 + 8);
  mov_r_m (reg_I4_free, m);
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0);
  mov_m_r (m, ebp);
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 4);
  mov_m_r (m, ecx);
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 8);
  mov_m_r (m, edx);
  /* recover callee saved registers and ret */
  ENCODER_FILL_END();
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf("code_block_switch_to_interp_from_jited:\n");
  dump_stream (code_block_switch_to_interp_from_jited,
               (int32)(stream - code_block_switch_to_interp_from_jited));
#endif

  code_block_switch_to_interp_from_jited_soe = stream;
  /* eax = JIT_INTERP_ACTION_SOE */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_SOE, true);
  mov_r_imm (eax, imm);
  imm_from_sz_v_s (imm, SZ8, stream_saved - stream - 2, true);
  jmp_imm (imm);
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_switch_to_interp_from_jited_soe:\n");
  dump_stream (code_block_switch_to_interp_from_jited_soe,
               (int32)(stream - code_block_switch_to_interp_from_jited_soe));
#endif

  code_block_switch_to_interp_from_jited_ae = stream;
  /* eax = JIT_INTERP_ACTION_AE */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_AE, true);
  mov_r_imm (eax, imm);
  imm_from_sz_v_s (imm, SZ8, stream_saved - stream - 2, true);
  jmp_imm (imm);
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_switch_to_interp_from_jited_ae:\n");
  dump_stream (code_block_switch_to_interp_from_jited_ae,
               (int32)(stream - code_block_switch_to_interp_from_jited_ae));
#endif


  code_block_switch_to_interp_from_jited_npe = stream;
  /* eax = JIT_INTERP_ACTION_NPE */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_NPE, true);
  mov_r_imm (eax, imm);
  imm_from_sz_v_s (imm, SZ8, stream_saved - stream - 2, true);
  jmp_imm (imm);
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_switch_to_interp_from_jited_npe:\n");
  dump_stream (code_block_switch_to_interp_from_jited_npe,
               (int32)(stream - code_block_switch_to_interp_from_jited_npe));
#endif

  code_block_switch_to_interp_from_jited_aioobe = stream;
  /* eax = JIT_INTERP_ACTION_AIOOBE */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_AIOOBE, true);
  mov_r_imm (eax, imm);
  imm_from_sz_v_s (imm, SZ8, stream_saved - stream - 2, true);
  jmp_imm (imm);
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_switch_to_interp_from_jited_aioobe:\n");
  dump_stream (code_block_switch_to_interp_from_jited_aioobe,
               (int32)(stream - code_block_switch_to_interp_from_jited_aioobe));
#endif

  code_block_switch_to_interp_from_jited_thrown = stream;
  /* eax = JIT_INTERP_ACTION_THROWN */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_THROWN, true);
  mov_r_imm (eax, imm);
  imm_from_sz_v_s (imm, SZ8, stream_saved - stream - 2, true);
  jmp_imm (imm);
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_switch_to_interp_from_jited_thrown:\n");
  dump_stream (code_block_switch_to_interp_from_jited_thrown,
               (int32)(stream - code_block_switch_to_interp_from_jited_thrown));
#endif

  code_block_call_to_interp_from_jited =
                    jit_code_cache_alloc (MAX_CODE_BLOCK_SIZE, "jited_call_interp");
  if (!code_block_call_to_interp_from_jited)
    goto free2;

  stream = code_block_call_to_interp_from_jited;
  /* info->frame = fp_reg */
  m_from_b_d (m, esp_reg, 16 + 8);
  mov_r_m (reg_I4_free, m);
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0);
  mov_m_r (m, ebp);
  /* info->method = method_reg */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 4);
  mov_m_r (m, eax);
  /* eax = JIT_INTERP_ACTION_CALL */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_CALL, true);
  mov_r_imm (eax, imm);
  /* recover callee saved registers and ret */
  ENCODER_FILL_END();
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf ("code_block_call_to_interp_from_jited:\n");
  dump_stream (code_block_call_to_interp_from_jited,
               (int32)(stream - code_block_call_to_interp_from_jited));
#endif

  code_block_return_to_interp_from_jited =
                    jit_code_cache_alloc (MAX_CODE_BLOCK_SIZE, "jited_return_interp");
  if (!code_block_return_to_interp_from_jited)
    goto free1;

  stream = code_block_return_to_interp_from_jited;
  /* info->frame = fp_reg */
  m_from_b_d (m, esp_reg, 16 + 8);
  mov_r_m (reg_I4_free, m);
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0);
  mov_m_r (m, ebp);
  /* info->out.ret.ival[0] = ecx */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 4);
  mov_m_r (m, ecx);
  /* info->out.ret.ival[1] = edx */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 8);
  mov_m_r (m, edx);

  /* ret_type (eax) == JIT_INTERP_ACTION_RET_F8 ? */
  imm_from_sz_v_s (imm, SZ32, JIT_INTERP_ACTION_RET_F8, true);
  alu_r_imm (cmp, eax, imm);
  imm_from_sz_v_s (imm, SZ8, 5, true);
  je (imm);
  /* ret_type == JIT_INTERP_ACTION_RET_F4, info->out.ret.ival[0] = st0 */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0xC);
  fst_m (m);
  imm_from_sz_v_s (imm, SZ8, 3, true);
  jmp_imm (imm);
  /* ret_type == JIT_INTERP_ACTION_RET_F8, info->out.ret.ival[0-1] = st0 */
  m_from_b_d (m, R_Opnd_get_reg_no (&reg_I4_free), 0xC);
  dst_m (m);

  /* recover callee saved registers and ret */
  ENCODER_FILL_END();
#ifdef CODEGEN_DUMP_LOWER_RESULT
  jit_printf("code_block_return_to_interp_from_jited:\n");
  dump_stream (code_block_return_to_interp_from_jited,
               (int32)(stream - code_block_return_to_interp_from_jited));
  jit_printf("\n");
  jit_printf(NULL);
#endif

  jit_globals.call_to_interp_from_jited = code_block_call_to_interp_from_jited;
  jit_globals.return_to_interp_from_jited = code_block_return_to_interp_from_jited;

  return true;

free1:
  jit_code_cache_free (code_block_call_to_interp_from_jited);
free2:
  jit_code_cache_free (code_block_switch_to_interp_from_jited);
free3:
  jit_code_cache_free (code_block_switch_to_jited_from_interp);

  return true;
}

/* Free begin code block */
static void
code_block_free ()
{
  if (code_block_switch_to_jited_from_interp)
    {
      jit_code_cache_free (code_block_switch_to_jited_from_interp);
      code_block_switch_to_jited_from_interp = NULL;
    }
  if (code_block_switch_to_interp_from_jited)
    {
      jit_code_cache_free (code_block_switch_to_interp_from_jited);
      code_block_switch_to_interp_from_jited = NULL;
    }
  if (code_block_call_to_interp_from_jited)
    {
      jit_code_cache_free (code_block_call_to_interp_from_jited);
      code_block_call_to_interp_from_jited = NULL;
    }
  if (code_block_return_to_interp_from_jited)
    {
      jit_code_cache_free (code_block_return_to_interp_from_jited);
      code_block_return_to_interp_from_jited = NULL;
    }
}

static const uint8 hreg_info_I4[3][7] =
  {
    {1, 0, 0, 0, 0, 0, 1},      /* fixed */
    {0, 0, 1, 1, 1, 0, 0},      /* caller_saved_native */
    {0, 0, 1, 1, 1, 1, 0}       /* caller_saved_jited */
  };

static uint8 hreg_info_F4[3][7] =
  {
    {0, 0, 0, 0, 1, 1, 1},      /* fixed */
    {1, 1, 1, 1, 1, 1, 1},      /* caller_saved_native */
    {1, 1, 1, 1, 1, 1, 1}       /* caller_saved_jited */
  };

static uint8 hreg_info_F8[3][7] =
  {
    {1, 1, 1, 1, 0, 0, 0},      /* fixed */
    {1, 1, 1, 1, 1, 1, 1},      /* caller_saved_native */
    {1, 1, 1, 1, 1, 1, 1}       /* caller_saved_jited */
  };

static const JitHardRegInfo hreg_info =
  {
    {
      {0, NULL, NULL, NULL},     /* VOID */

      {sizeof (hreg_info_I4[0]), /* I4 */
       hreg_info_I4[0],
       hreg_info_I4[1],
       hreg_info_I4[2]},

      {0, NULL, NULL, NULL},     /* I8 */

      {sizeof (hreg_info_F4[0]), /* F4 */
       hreg_info_F4[0],
       hreg_info_F4[1],
       hreg_info_F4[2]},

      {sizeof (hreg_info_F8[0]), /* F8 */
       hreg_info_F8[0],
       hreg_info_F8[1],
       hreg_info_F8[2]},

      {0, NULL, NULL, NULL},    /* V8 */
      {0, NULL, NULL, NULL},    /* V16 */
      {0, NULL, NULL, NULL}     /* V32 */
    },
    0, 1, 6
  };

const JitHardRegInfo*
jit_codegen_x86_get_hreg_info ()
{
  return &hreg_info;
}

bool
jit_codegen_x86_init ()
{
  bool ret;

  regs_init ();

  ret = encoder_init ();
  if (!ret)
    return ret;

  ret = code_block_init ();
  if (!ret) {
    encoder_destroy ();
  }

  return ret;
}

void
jit_codegen_x86_destroy ()
{
  code_block_free ();
  encoder_destroy ();
}

bool
jit_codegen_x86_aot_relocate (const JitAotRegionHeader *region,
                              void *method, void *code_ptr)
{
  const AotRelocRecord *r =
    (AotRelocRecord *)((uint8 *)region + sizeof (*region)
                       + region->native_code_size);
  const AotRelocRecord *end =
    (AotRelocRecord *)((uint8 *)r + region->relocation_size);
  uint8 *code = (uint8 *)code_ptr;
  unsigned cur_ip, val;

  for (; r < end; r++)
    switch (r->relocation_type & 0x0f)
      {
      case 1:
        val = jit_frontend_aot_reloc_value (method, r->relocation_data);

        if ((val & ~0xff))
          return false;
        else
          *(code + r->offset) = val;

        break;

      case 2:
        val = jit_frontend_aot_reloc_value (method, r->relocation_data);

        if ((val & ~0xffff))
          return false;
        else
          *(uint16 *)(code + r->offset) = val;

        break;

      case 4:
        if ((r->relocation_type & AOT_RELOC_JMP_TARGET_CODE))
          cur_ip = (unsigned) (code + r->offset + 4);
        else
          cur_ip = 0;

        if ((r->relocation_type & AOT_RELOC_CODE_BLOCK))
          val = (unsigned)interp_action_to_code_block (r->relocation_data);
        else if ((r->relocation_type & AOT_RELOC_RETURN_ADDRESS))
          val = (unsigned)(code + r->offset + 4 + 3);
        else
          val = jit_frontend_aot_reloc_value (method, r->relocation_data);

        *(uint32 *)(code + r->offset) = val - cur_ip;
        break;

      default:
        jit_assert (0);
      }

  return true;
}
