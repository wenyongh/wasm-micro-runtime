#include "jit_codegen.h"

bool
jit_codegen_init()
{
    return false;
}

void
jit_codegen_destroy()
{}

const JitHardRegInfo *
jit_codegen_get_hreg_info()
{
    return NULL;
}

bool
jit_codegen_gen_native(JitCompContext *cc)
{
    return false;
}

bool
jit_codegen_lower(JitCompContext *cc)
{
    return false;
}

void
jit_codegen_dump_native(void *begin_addr, void *end_addr)
{}

bool
jit_codegen_call_func_jited(void *exec_env, void *frame, void *target)
{
    return false;
}
