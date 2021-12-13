#include "jit_dump.h"
#include "jit_compiler.h"
#include "jit_codegen.h"

void
jit_dump_reg(JitCompContext *cc, JitReg reg)
{
    unsigned kind = jit_reg_kind(reg);
    unsigned no = jit_reg_no(reg);

    switch (kind) {
        case JIT_REG_KIND_VOID:
            os_printf("VOID");
            break;

        case JIT_REG_KIND_I32:
            if (jit_reg_is_const(reg)) {
                unsigned rel = jit_cc_get_const_I32_rel(cc, reg);

                os_printf("0x%x", jit_cc_get_const_I32(cc, reg));

                if (rel)
                    os_printf("(rel: 0x%x)", rel);
            }
            else
                os_printf("i%d", no);
            break;

        case JIT_REG_KIND_I64:
            if (jit_reg_is_const(reg))
                os_printf("0x%llxL", jit_cc_get_const_I64(cc, reg));
            else
                os_printf("l%d", no);
            break;

        case JIT_REG_KIND_F32:
            if (jit_reg_is_const(reg))
                os_printf("%f", jit_cc_get_const_F32(cc, reg));
            else
                os_printf("f%d", no);
            break;

        case JIT_REG_KIND_F64:
            if (jit_reg_is_const(reg))
                os_printf("%fL", jit_cc_get_const_F64(cc, reg));
            else
                os_printf("d%d", no);
            break;

        case JIT_REG_KIND_L32:
            os_printf("L%d", no);
            break;

        default:
            bh_assert(!"Unsupported register kind.");
    }
}

static void
jit_dump_insn_Reg(JitCompContext *cc, JitInsn *insn, unsigned opnd_num)
{
    unsigned i;

    for (i = 0; i < opnd_num; i++) {
        os_printf(i == 0 ? " " : ", ");
        jit_dump_reg(cc, *(jit_insn_opnd(insn, i)));
    }

    os_printf("\n");
}

static void
jit_dump_insn_VReg(JitCompContext *cc, JitInsn *insn, unsigned opnd_num)
{
    unsigned i;

    opnd_num = jit_insn_opndv_num(insn);

    for (i = 0; i < opnd_num; i++) {
        os_printf(i == 0 ? " " : ", ");
        jit_dump_reg(cc, *(jit_insn_opndv(insn, i)));
    }

    os_printf("\n");
}

static void
jit_dump_insn_TableSwitch(JitCompContext *cc, JitInsn *insn, unsigned opnd_num)
{
    int i;
    JitOpndTableSwitch *opnd = jit_insn_opndts(insn);

    os_printf(" ");
    jit_dump_reg(cc, opnd->value);
    os_printf("\n%16s: ", "default");
    jit_dump_reg(cc, opnd->default_target);
    os_printf("\n");

    for (i = opnd->low_value; i <= opnd->high_value; i++) {
        os_printf("%18d: ", i);
        jit_dump_reg(cc, opnd->targets[i - opnd->low_value]);
        os_printf("\n");
    }
}

static void
jit_dump_insn_LookupSwitch(JitCompContext *cc, JitInsn *insn, unsigned opnd_num)
{
    unsigned i;
    JitOpndLookupSwitch *opnd = jit_insn_opndls(insn);

    os_printf(" ");
    jit_dump_reg(cc, opnd->value);
    os_printf("\n%16s: ", "default");
    jit_dump_reg(cc, opnd->default_target);
    os_printf("\n");

    for (i = 0; i < opnd->match_pairs_num; i++) {
        os_printf("%18d: ", opnd->match_pairs[i].value);
        jit_dump_reg(cc, opnd->match_pairs[i].target);
        os_printf("\n");
    }
}

void
jit_dump_insn(JitCompContext *cc, JitInsn *insn)
{
    switch (insn->opcode) {
#define INSN(NAME, OPND_KIND, OPND_NUM, FIRST_USE)     \
    case JIT_OP_##NAME:                                \
        os_printf("    %-15s", #NAME);                 \
        jit_dump_insn_##OPND_KIND(cc, insn, OPND_NUM); \
        break;
#include "jit_ir.def"
#undef INSN
    }
}

void
jit_dump_basic_block(JitCompContext *cc, JitBasicBlock *block)
{
    unsigned i;
    JitInsn *insn;
    JitRegVec preds = jit_basic_block_preds(block);
    JitRegVec succs = jit_basic_block_succs(block);
    JitReg label = jit_basic_block_label(block);
    JitReg *reg;

    jit_dump_reg(cc, label);
    os_printf(":\n    ; PREDS(");

    JIT_REG_VEC_FOREACH(preds, i, reg)
    {
        if (i > 0)
            os_printf(" ");
        jit_dump_reg(cc, *reg);
    }

    os_printf(")\n    ; FREQ=%d", *(jit_annl_freq(cc, label)));

    if (jit_annl_is_enabled_begin_bcip(cc))
        os_printf(" BEGIN_BCIP=%d", *(jit_annl_begin_bcip(cc, label))
                                        - (uint8 *)cc->wasm_func->code);

    if (jit_annl_is_enabled_end_bcip(cc))
        os_printf(" END_BCIP=%d", *(jit_annl_end_bcip(cc, label))
                                      - (uint8 *)cc->wasm_func->code);
    os_printf("\n");

    if (jit_annl_is_enabled_jited_addr(cc))
        /* Dump assembly.  */
        jit_codegen_dump_native(*(jit_annl_jited_addr(cc, label)),
                                label != cc->exit_label ? *(jit_annl_jited_addr(
                                    cc, *(jit_annl_next_label(cc, label))))
                                                        : cc->jited_addr_end);
    else
        /* Dump IR.  */
        JIT_FOREACH_INSN(block, insn)
    jit_dump_insn(cc, insn);

    os_printf("    ; SUCCS(");

    JIT_REG_VEC_FOREACH(succs, i, reg)
    {
        if (i > 0)
            os_printf(" ");
        jit_dump_reg(cc, *reg);
    }

    os_printf(")\n\n");
}

static void
dump_func_name(JitCompContext *cc)
{
    const char *func_name = NULL;
    WASMModule *module = cc->wasm_module;

#if WASM_ENABLE_CUSTOM_NAME_SECTION != 0
    func_name = func->field_name;
#endif

    /* if custom name section is not generated,
       search symbols from export table */
    if (!func_name) {
        uint32 i;
        for (i = 0; i < module->export_count; i++) {
            if (module->exports[i].kind == EXPORT_KIND_FUNC
                && module->exports[i].index == cc->wasm_func_idx) {
                func_name = module->exports[i].name;
                break;
            }
        }
    }

    /* function name not exported, print number instead */
    if (func_name == NULL) {
        os_printf("$f%d", cc->wasm_func_idx);
    }
    else {
        os_printf("%s", func_name);
    }
}

static void
dump_cc_ir(JitCompContext *cc)
{
    unsigned i, end;
    JitBasicBlock *block;
    JitReg label;
    const char *kind_names[] = { "VOID", "I32", "I64",  "F32",
                                 "F64",  "V64", "V128", "V256" };

    os_printf("; Function: ");
    dump_func_name(cc);
    os_printf("\n");

    os_printf("; Constant table sizes:");

    for (i = 0; i < JIT_REG_KIND_L32; i++)
        os_printf(" %s=%d", kind_names[i], cc->_const_val._num[i]);

    os_printf("\n; Label number: %d", jit_cc_label_num(cc));
    os_printf("\n; Instruction number: %d", jit_cc_insn_num(cc));
    os_printf("\n; Register numbers:");

    for (i = 0; i < JIT_REG_KIND_L32; i++)
        os_printf(" %s=%d", kind_names[i], jit_cc_reg_num(cc, i));

    os_printf("\n; Label annotations:");
#define ANN_LABEL(TYPE, NAME)           \
    if (jit_annl_is_enabled_##NAME(cc)) \
        os_printf(" %s", #NAME);
#include "jit_ir.def"
#undef ANN_LABEL

    os_printf("\n; Instruction annotations:");
#define ANN_INSN(TYPE, NAME)            \
    if (jit_anni_is_enabled_##NAME(cc)) \
        os_printf(" %s", #NAME);
#include "jit_ir.def"
#undef ANN_INSN

    os_printf("\n; Register annotations:");
#define ANN_REG(TYPE, NAME)             \
    if (jit_annr_is_enabled_##NAME(cc)) \
        os_printf(" %s", #NAME);
#include "jit_ir.def"
#undef ANN_REG

    os_printf("\n\n");

    if (jit_annl_is_enabled_next_label(cc))
        /* Blocks have been reordered, use that order to dump.  */
        for (label = cc->entry_label; label;
             label = *(jit_annl_next_label(cc, label)))
            jit_dump_basic_block(cc, *(jit_annl_basic_block(cc, label)));
    else
    /* Otherwise, use the default order.  */
    {
        jit_dump_basic_block(cc, jit_cc_entry_basic_block(cc));

        JIT_FOREACH_BLOCK(cc, i, end, block)
        jit_dump_basic_block(cc, block);

        jit_dump_basic_block(cc, jit_cc_exit_basic_block(cc));
    }
}

void
jit_dump_cc(JitCompContext *cc)
{
    if (jit_cc_label_num(cc) <= 2)
        return;

    dump_cc_ir(cc);
}

bool
_jit_pass_dump(JitCompContext *cc)
{
    os_printf(
        "JIT.COMPILER.DUMP: PASS_NO=%d PREV_PASS=%s\n\n", cc->pass_no,
        (cc->pass_no > 0 ? jit_compiler_get_pass_name(cc->pass_no) : "NULL"));
    jit_dump_cc(cc);
    os_printf("\n");
    return true;
}

bool
_jit_pass_update_cfg(JitCompContext *cc)
{
    return jit_cc_update_cfg(cc);
}
