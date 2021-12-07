#ifndef _JIT_COMPILER_H_
#define _JIT_COMPILER_H_

#include "bh_platform.h"
#include "../interpreter/wasm.h"
#include "jit_ir.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Internal error codes.
 */
enum {
    JIT_ERROR_OOM = 1,          /* out-of-memory */
    JIT_ERROR_UNSUPPORTED_HREG, /* unsupported register */
    JIT_ERROR_UNSUPPORTED_OP,   /* unsupported operation */
    JIT_ERROR_UNSUPPORTED_RELOC /* unsupported relocation */
};

bool
jit_compiler_init();

void
jit_compiler_destroy();

bool
jit_compiler_compile(WASMModule *module, uint32 func_idx);

bool
jit_compiler_compile_all(WASMModule *module);

/*
 * Pass declarations:
 */

/**
 * Dump the compilation context.
 */
bool
_jit_pass_dump(JitCompContext *cc);

/**
 * Update CFG (usually before dump for better readability).
 */
bool
_jit_pass_update_cfg(JitCompContext *cc);

/**
 * Translate profiling result into MIR.
 */
bool
_jit_pass_frontend(JitCompContext *cc);

/**
 * Convert MIR to LIR.
 */
bool
_jit_pass_lower_fe(JitCompContext *cc);

/**
 * Lower unsupported operations into supported ones.
 */
bool
_jit_pass_lower_cg(JitCompContext *cc);

/**
 * Register allocation.
 */
bool
_jit_pass_regalloc(JitCompContext *cc);

/**
 * Basic block reordering optimization that attempts to reorder basic
 * blocks to minimize cost of branch instructions.
 */
bool
_jit_pass_bbreorder(JitCompContext *cc);

/**
 * Native code generation.
 */
bool
_jit_pass_codegen(JitCompContext *cc);

/**
 * Register the region so that it can be executed.
 */
bool
_jit_pass_register_region(JitCompContext *cc);

#ifdef __cplusplus
}
#endif

#endif /* end of _JIT_COMPILER_H_ */
