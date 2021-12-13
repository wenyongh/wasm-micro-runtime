#include "jit_compiler.h"
#include "jit_frontend.h"

/**
 * A stack storing non-null JitBasicBlock pointers.
 */
typedef struct BlockStack {
    JitBasicBlock **base;
    JitBasicBlock **top;
    uint32 capacity;
} BlockStack;

static bool
block_stack_init(BlockStack *stack, unsigned capacity)
{
    stack->capacity = capacity;
    stack->base = stack->top = jit_malloc(sizeof(*stack->base) * capacity);
    return stack->base != NULL;
}

static void
block_stack_destroy(BlockStack *stack)
{
    jit_free(stack->base);
}

static bool
block_stack_push(BlockStack *stack, JitBasicBlock *block)
{
    if (stack->top == stack->base + stack->capacity) {
        unsigned capacity = stack->capacity + stack->capacity / 2;
        JitBasicBlock **base = jit_malloc(sizeof(*base) * capacity);

        if (!base)
            return false;

        memcpy(base, stack->base, sizeof(*stack->base) * stack->capacity);
        jit_free(stack->base);
        stack->base = base;
        stack->top = stack->base + stack->capacity;
        stack->capacity = capacity;
    }

    *stack->top++ = block;
    return true;
}

static JitBasicBlock *
block_stack_pop(BlockStack *stack)
{
    if (stack->top > stack->base)
        return *--stack->top;
    else
        return NULL;
}

static JitBasicBlock *
translate_block(JitCompContext *cc, uint8 *bcip, JitBitmap *is_reached)
{
    JitBasicBlock *block = jit_frontend_translate_block(cc, bcip, is_reached);
    /* Reset the hash table after each block's translation. */
    jit_cc_reset_insn_hash(cc);
    return block;
}

/**
 * Helper function for form_and_translate_region. It translates
 * successors of the cur_block that need to be translated and it
 * connects the cur_block to them and push them onto stack.
 */
static bool
handle_one_block(JitCompContext *cc, JitBasicBlock *cur_block,
                 const uint8 *first_bcip, const uint8 *last_bcip,
                 JitBasicBlock **bbmap, JitBitmap *is_reached,
                 BlockStack *stack)
{
    const JitReg cur_label = jit_basic_block_label(cur_block);
    const JitRegVec succs = jit_basic_block_succs(cur_block);
    unsigned succ_index;
    JitReg *target;

    JIT_REG_VEC_FOREACH(succs, succ_index, target)
    {
        uint8 *end_bcip, *target_bcip;

        bh_assert(jit_reg_is_value(*target));

        if (!jit_reg_is_const(*target))
            /* Constant value here after frontend translation
               indicates that the target needs to be redirected. */
            continue;

        end_bcip = *(jit_annl_end_bcip(cc, cur_label));
        target_bcip = end_bcip + jit_cc_get_const_I32(cc, *target);

        /* translate the target block and connect to it. */
        {
            unsigned offset = target_bcip - first_bcip;

            if (!bbmap[offset])
            /* It's not translated yet, translate it and push it
               onto stack. */
            {
                /* Fill in the information for block translation. */
                /*entry.sp = *(jit_annl_end_sp(cc, cur_label));*/

                /* Translate the target block. */
                if (!(bbmap[offset] =
                          translate_block(cc, target_bcip, is_reached)))
                    return false;

                /* Push it onto stack. */
                if (!block_stack_push(stack, bbmap[offset]))
                    return false;
            }

            /* Redirect the target to the new block. */
            *target = jit_basic_block_label(bbmap[offset]);
        }
    }

    return true;
}

/**
 * Form the region by translating blocks that are reached from the
 * region entry block through hot edges.
 *
 * @param cc the compilation context
 *
 * @return is_reached bitmap indicating whether a bcip is reached as a
 * block entry if succeeds, NULL otherwise
 */
static JitBitmap *
form_and_translate_region(JitCompContext *cc)
{
    uint8 *first_bcip = cc->wasm_func->code;
    uint8 *last_bcip = cc->wasm_func->code + cc->wasm_func->code_size;
    const unsigned bbmap_size = last_bcip - first_bcip + 1;
    JitBasicBlock **bbmap = NULL;
    JitBitmap *is_reached = NULL, *is_reached_ret = NULL;
    JitBasicBlock *cur_block;
    BlockStack stack = { NULL, NULL, 0 };
    JitInsn *jmp_insn;
    JitReg region_entry_label;

    if (!block_stack_init(&stack, bbmap_size / 32 + 4))
        return NULL;

    /* Create a map that maps bytecode offsets to blocks. */
    if (!(bbmap = jit_calloc(sizeof(*bbmap) * bbmap_size)))
        goto cleanup_and_return;

    /* Create a reached bitmap. */
    if (!(is_reached = jit_bitmap_new((uintptr_t)first_bcip, bbmap_size)))
        goto cleanup_and_return;

    /* Translate the region entry block. */
    if (!(bbmap[0] = translate_block(cc, first_bcip, is_reached)))
        goto cleanup_and_return;

    /* The label of the region entry. */
    region_entry_label = jit_basic_block_label(bbmap[0]);

    /* Create a JMP instruction jumping to the region entry. */
    if (!(jmp_insn = jit_cc_new_insn(cc, JMP, region_entry_label)))
        goto cleanup_and_return;

    /* Insert the instruction into the cc entry block. */
    jit_basic_block_append_insn(jit_cc_entry_basic_block(cc), jmp_insn);

    /* Push the block onto working stack. */
    if (!block_stack_push(&stack, bbmap[0]))
        goto cleanup_and_return;

    while ((cur_block = block_stack_pop(&stack)))
        if (!handle_one_block(cc, cur_block, first_bcip, last_bcip, bbmap,
                              is_reached, &stack))
            goto cleanup_and_return;

    is_reached_ret = is_reached;
    is_reached = NULL;

cleanup_and_return:
    block_stack_destroy(&stack);
    jit_free(bbmap);
    jit_bitmap_delete(is_reached);
    jit_frontend_translate_block(cc, NULL, NULL);
    return is_reached_ret;
}

bool
_jit_pass_frontend(JitCompContext *cc)
{
    JitBitmap *is_reached = NULL;
    bool retval = false;

    /* Enable necessary annotations required at the current stage. */
    if (!jit_annl_enable_freq(cc) || !jit_annl_enable_begin_bcip(cc)
        || !jit_annl_enable_end_bcip(cc) || !jit_annl_enable_end_sp(cc)
        || !jit_annr_enable_def_insn(cc) || !jit_cc_enable_insn_hash(cc, 127))
        goto fail;

    if (!(is_reached = form_and_translate_region(cc)))
        goto fail;

    /* Release the annotations after local CSE and translation. */
    jit_cc_disable_insn_hash(cc);
    jit_annl_disable_end_sp(cc);
    retval = true;

fail:
    jit_bitmap_delete(is_reached);
    return retval;
}

bool
_jit_pass_lower_fe(JitCompContext *cc)
{
    /* Lowering pass won't maintain the def_insn annotation of registers
       so disable it to avoid potential abuses. */
    jit_annr_disable_def_insn(cc);

    return jit_frontend_lower(cc);
}

/**
 * Helper function for GEN_INSN
 *
 * @param cc compilation context
 * @param block the current block
 * @param insn the new instruction
 *
 * @return the new instruction if inserted, NULL otherwise
 */
static inline JitInsn *
_gen_insn(JitCompContext *cc, JitBasicBlock *block, JitInsn *insn)
{
    if (insn)
        jit_basic_block_append_insn(block, insn);

    return insn;
}

/**
 * Generate and append an instruction to the current block.
 */
#define GEN_INSN(...) _gen_insn(cc, block, jit_cc_new_insn(cc, __VA_ARGS__))

/**
 * Create a constant register without relocation info.
 *
 * @param Type type of the register
 * @param val the constant value
 *
 * @return the constant register if succeeds, 0 otherwise
 */
#define NEW_CONST(Type, val) jit_cc_new_const_##Type(cc, val)

JitBasicBlock *
jit_frontend_translate_block(JitCompContext *cc, uint8 *bcip,
                             JitBitmap *is_reached)
{
    printf("##jit_frontend_translate_block\n");

    JitBasicBlock *block = jit_cc_new_basic_block(cc, 0);
    JitReg r1 = jit_cc_new_reg_I32(cc);
    JitReg r2 = jit_cc_new_reg_I32(cc);
    JitReg r3 = jit_cc_new_reg_I64(cc);
    JitReg r4 = jit_cc_new_reg_I32(cc);
    JitReg r5 = jit_cc_new_reg_I64(cc);
    GEN_INSN(MOV, r2, r1);
    GEN_INSN(MOV, r3, cc->fp_reg);
    GEN_INSN(LDI32, r4, cc->fp_reg, NEW_CONST(I32, 16));
    GEN_INSN(LDI64, r5, cc->exec_env_reg, NEW_CONST(I32, 32));

    return block;
}
