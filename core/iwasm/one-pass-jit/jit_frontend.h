#ifndef _JIT_FRONTEND_H_
#define _JIT_FRONTEND_H_

#include "jit_utils.h"
#include "jit_ir.h"

/**
 * Translate instructions in a basic block starting at the given entry
 * and ending before the given end bcip. The translated block must
 * end with a branch instruction whose targets are offsets relating to
 * the end bcip of the translated block, which are integral constants.
 * If a target of a branch is really a constant value (which should be
 * rare), put it into a register and then jump to the register instead
 * of using the constant value directly in the target. In the
 * translation process, don't create any new labels. The code bcip of
 * the begin and end of the translated block is stored in the
 * jit_annl_begin_bcip and jit_annl_end_bcip annotations of the label
 * of the block, which must be the same as the bcips used in
 * profiling.
 *
 * NOTE: the function must explicitly set SP to correct value when the
 * entry's bcip is the function's entry address.
 *
 * @param cc containing compilation context of generated IR
 * @param entry entry of the basic block to be translated. If its
 * value is NULL, the function will clean up any pass local data that
 * might be created previously.
 * @param is_reached a bitmap recording which bytecode has been
 * reached as a block entry
 *
 * @return IR block containing translated instructions if succeeds,
 * NULL otherwise
 */
JitBasicBlock *
jit_frontend_translate_block(JitCompContext *cc, uint8 *bcip,
                             JitBitmap *is_reached);

/**
 * Generate a block leaving the compiled code, which must store the
 * target bcip and other necessary information for switching to
 * interpreter or other compiled code and then jump to the exit of the
 * cc.
 *
 * @param cc the compilation context
 * @param bcip the target bytecode instruction pointer
 * @param sp_offset stack pointer offset at the beginning of the block
 *
 * @return the leaving block if succeeds, NULL otherwise
 */
JitBlock *
jit_frontend_gen_leaving_block(JitCompContext *cc, void *bcip,
                               unsigned sp_offset);

#if 0
/**
 * Print the qualified name of the given function.
 *
 * @param function the function whose name to be printed
 */
void
jit_frontend_print_function_name(void *function);

/**
 * Get the full name of the function.  If the input buffer lengh
 * is less than the actual function name length, the function will
 * simply return the actuall length and won't write to the buffer.
 *
 * @param function pointer to a function
 * @param buf buffer for the returned name
 * @param buf_len lengh of the buffer
 *
 * @return actual length of the name
 */
unsigned
jit_frontend_get_function_name(void *function, char *buf, unsigned buf_len);

/**
 * Convert the bcip in the given function to an internal offset.
 *
 * @param function function containing the bcip
 * @param bcip bytecode instruction pointer
 *
 * @return converted offset of the bcip
 */
unsigned
jit_frontend_bcip_to_offset(void *function, void *bcip);
#endif

/**
 * Lower the IR of the given compilation context.
 *
 * @param cc the compilation context
 *
 * @return true if succeeds, false otherwise
 */
bool
jit_frontend_lower(JitCompContext *cc);

#endif
