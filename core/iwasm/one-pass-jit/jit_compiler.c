#include "jit_compiler.h"
#include "jit_ir.h"
#include "jit_codegen.h"
#include "jit_codecache.h"
#include "../interpreter/wasm.h"

typedef struct JitGlobals {
    /* Compiler pass sequence.  The last element must be 0.  */
    const uint8 *passes;
    /* Code cache size.  */
    uint32 code_cache_size;
} JitGlobals;

/* The exported global data of JIT compiler.  */
JitGlobals jit_globals;

typedef struct JitCompilerPass {
    /* Name of the pass.  */
    const char *name;

    /* The entry of the compiler pass.  */
    bool (*run)(JitCompContext *cc);
} JitCompilerPass;

#define REG_PASS(name) { #name, _jit_pass_##name },

/* clang-format off */
static JitCompilerPass compiler_passes[] = {
    { NULL, NULL },
    REG_PASS(dump)
    /*REG_PASS(update_cfg)*/
    REG_PASS(frontend)
    REG_PASS(lower_fe)
    REG_PASS(lower_cg)
    REG_PASS(regalloc)
    REG_PASS(codegen)
    REG_PASS(register_region)
};
/* clang-format on */

#undef REG_PASS

/* Number of compiler passes.  */
#define COMPILER_PASS_NUM (sizeof(compiler_passes) / sizeof(compiler_passes[0]))

static bool
apply_compiler_passes(JitCompContext *cc)
{
    const uint8 *p = jit_globals.passes;

    for (; *p; p++) {
        /* Set the pass NO.  */
        cc->pass_no = p - jit_globals.passes;
        bh_assert(*p < COMPILER_PASS_NUM);

        if (!compiler_passes[*p].run(cc)) {
            LOG_VERBOSE("JIT: compilation failed at pass[%d] = %s\n",
                        p - jit_globals.passes, compiler_passes[*p].name);
            return false;
        }
    }

    return true;
}

bool
jit_compiler_init()
{
    /* TODO: get code cache size with global configs */
    if (!jit_code_cache_init(2 * 1024 * 1024))
        return false;

    if (!jit_codegen_init())
        goto fail1;

    return true;

fail1:
    jit_code_cache_destroy();
    return false;
}

void
jit_compiler_destroy()
{
    jit_codegen_destroy();

    jit_code_cache_destroy();
}

const char *
jit_compiler_get_pass_name(unsigned i)
{
    return i < COMPILER_PASS_NUM ? compiler_passes[i].name : NULL;
}

static bool
is_fatal_error(unsigned error_code)
{
    switch (error_code) {
        case JIT_ERROR_OOM:
        case JIT_ERROR_UNSUPPORTED_HREG:
        case JIT_ERROR_UNSUPPORTED_OP:
            return true;

        default:
            return false;
    }
}

bool
jit_compiler_compile(WASMModule *module, uint32 func_idx)
{
    JitCompContext *cc;
    bool ret = false;

    /* Initialize compilation context.  */
    if (!(cc = jit_calloc(sizeof(*cc))))
        return false;

    if (!jit_cc_init(cc, 64)) {
        jit_free(cc);
        return false;
    }

    /* TODO: create function contex */

    /* Apply compiler passes.  */
    if (apply_compiler_passes(cc))
        ret = true;

    /* Delete the compilation context.  */
    jit_cc_delete(cc);

    return ret;
}

bool
jit_compiler_compile_all(WASMModule *module)
{
    JitCompContext *cc;
    bool ret = false;

    /* Initialize compilation context.  */
    if (!(cc = jit_calloc(sizeof(*cc))))
        return false;

    if (!jit_cc_init(cc, 64)) {
        jit_free(cc);
        return false;
    }

    /* TODO: create function contex */

    /* Apply compiler passes.  */
    if (apply_compiler_passes(cc))
        ret = true;

    /* Delete the compilation context.  */
    jit_cc_delete(cc);

    return ret;
}

bool
jit_call_func_jited(void *exec_env, void *frame, void *target)
{
    return jit_codegen_call_func_jited(exec_env, frame, target);
}
