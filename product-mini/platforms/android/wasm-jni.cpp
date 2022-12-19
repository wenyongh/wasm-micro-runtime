#include <cstring>
#include <stdlib.h>
#include <jni.h>
#include <cinttypes>
#include <android/log.h>
#include <string>
#include <wasm_export.h>

#define LOGI(...) \
    ((void)__android_log_print(ANDROID_LOG_INFO, "wasm_jni::", __VA_ARGS__))

static void *
app_instance_main(wasm_module_inst_t module_inst)
{
    const char *exception;

    wasm_application_execute_main(module_inst, 0, NULL);
    if ((exception = wasm_runtime_get_exception(module_inst)))
        LOGI("%s\n", exception);
    return NULL;
}

// WARNING! CAN NOT BE READ ONLY!!!
static unsigned char wasm_test_file[] = {
    0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x01, 0x10, 0x03, 0x60,
    0x01, 0x7F, 0x01, 0x7F, 0x60, 0x02, 0x7F, 0x7F, 0x01, 0x7F, 0x60, 0x01,
    0x7F, 0x00, 0x02, 0x31, 0x04, 0x03, 0x65, 0x6E, 0x76, 0x04, 0x70, 0x75,
    0x74, 0x73, 0x00, 0x00, 0x03, 0x65, 0x6E, 0x76, 0x06, 0x6D, 0x61, 0x6C,
    0x6C, 0x6F, 0x63, 0x00, 0x00, 0x03, 0x65, 0x6E, 0x76, 0x06, 0x70, 0x72,
    0x69, 0x6E, 0x74, 0x66, 0x00, 0x01, 0x03, 0x65, 0x6E, 0x76, 0x04, 0x66,
    0x72, 0x65, 0x65, 0x00, 0x02, 0x03, 0x02, 0x01, 0x01, 0x04, 0x05, 0x01,
    0x70, 0x01, 0x01, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x06, 0x13, 0x03,
    0x7F, 0x01, 0x41, 0xC0, 0x28, 0x0B, 0x7F, 0x00, 0x41, 0xBA, 0x08, 0x0B,
    0x7F, 0x00, 0x41, 0xC0, 0x28, 0x0B, 0x07, 0x2C, 0x04, 0x06, 0x6D, 0x65,
    0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00, 0x0A, 0x5F, 0x5F, 0x64, 0x61, 0x74,
    0x61, 0x5F, 0x65, 0x6E, 0x64, 0x03, 0x01, 0x0B, 0x5F, 0x5F, 0x68, 0x65,
    0x61, 0x70, 0x5F, 0x62, 0x61, 0x73, 0x65, 0x03, 0x02, 0x04, 0x6D, 0x61,
    0x69, 0x6E, 0x00, 0x04, 0x0A, 0xB2, 0x01, 0x01, 0xAF, 0x01, 0x01, 0x03,
    0x7F, 0x23, 0x80, 0x80, 0x80, 0x80, 0x00, 0x41, 0x20, 0x6B, 0x22, 0x02,
    0x24, 0x80, 0x80, 0x80, 0x80, 0x00, 0x41, 0x9B, 0x88, 0x80, 0x80, 0x00,
    0x10, 0x80, 0x80, 0x80, 0x80, 0x00, 0x1A, 0x02, 0x40, 0x02, 0x40, 0x41,
    0x80, 0x08, 0x10, 0x81, 0x80, 0x80, 0x80, 0x00, 0x22, 0x03, 0x0D, 0x00,
    0x41, 0xA8, 0x88, 0x80, 0x80, 0x00, 0x10, 0x80, 0x80, 0x80, 0x80, 0x00,
    0x1A, 0x41, 0x7F, 0x21, 0x04, 0x0C, 0x01, 0x0B, 0x20, 0x02, 0x20, 0x03,
    0x36, 0x02, 0x10, 0x41, 0x80, 0x88, 0x80, 0x80, 0x00, 0x20, 0x02, 0x41,
    0x10, 0x6A, 0x10, 0x82, 0x80, 0x80, 0x80, 0x00, 0x1A, 0x41, 0x00, 0x21,
    0x04, 0x20, 0x03, 0x41, 0x04, 0x6A, 0x41, 0x00, 0x2F, 0x00, 0x91, 0x88,
    0x80, 0x80, 0x00, 0x3B, 0x00, 0x00, 0x20, 0x03, 0x41, 0x00, 0x28, 0x00,
    0x8D, 0x88, 0x80, 0x80, 0x00, 0x36, 0x00, 0x00, 0x20, 0x02, 0x20, 0x03,
    0x36, 0x02, 0x00, 0x41, 0x93, 0x88, 0x80, 0x80, 0x00, 0x20, 0x02, 0x10,
    0x82, 0x80, 0x80, 0x80, 0x00, 0x1A, 0x20, 0x03, 0x10, 0x83, 0x80, 0x80,
    0x80, 0x00, 0x0B, 0x20, 0x02, 0x41, 0x20, 0x6A, 0x24, 0x80, 0x80, 0x80,
    0x80, 0x00, 0x20, 0x04, 0x0B, 0x0B, 0x41, 0x01, 0x00, 0x41, 0x80, 0x08,
    0x0B, 0x3A, 0x62, 0x75, 0x66, 0x20, 0x70, 0x74, 0x72, 0x3A, 0x20, 0x25,
    0x70, 0x0A, 0x00, 0x31, 0x32, 0x33, 0x34, 0x0A, 0x00, 0x62, 0x75, 0x66,
    0x3A, 0x20, 0x25, 0x73, 0x00, 0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x77,
    0x6F, 0x72, 0x6C, 0x64, 0x21, 0x00, 0x6D, 0x61, 0x6C, 0x6C, 0x6F, 0x63,
    0x20, 0x62, 0x75, 0x66, 0x20, 0x66, 0x61, 0x69, 0x6C, 0x65, 0x64, 0x00
};

extern "C" JNIEXPORT void JNICALL
Java_com_intel_wasm_api_Runtime_run(JNIEnv *env, jclass thiz)
{
    wasm_module_t wasm_module = NULL;
    wasm_module_inst_t wasm_module_inst = NULL;
    RuntimeInitArgs init_args;
    uint wasm_file_size = 0;
    uint8_t *wasm_file_buf = NULL;
    char error_buf[128] = { 0 };

    memset(&init_args, 0, sizeof(RuntimeInitArgs));

#if WASM_ENABLE_GLOBAL_HEAP_POOL == 0
    init_args.mem_alloc_type = Alloc_With_Allocator;
    init_args.mem_alloc_option.allocator.malloc_func = (void *)malloc;
    init_args.mem_alloc_option.allocator.realloc_func = (void *)realloc;
    init_args.mem_alloc_option.allocator.free_func = (void *)free;
#else
#error The usage of a global heap pool is not implemented yet for Android.
#endif

    LOGI("wasm_runtime_full_init");
    /* initialize runtime environment */
    if (!wasm_runtime_full_init(&init_args)) {
        LOGI("Init runtime failed.\n");
        return;
    }

    /* load WASM byte buffer from a preinstall WASM bin file */
    LOGI("use an internal test file, gona to output Hello World in logcat\n");
    wasm_file_buf = (uint8_t *)wasm_test_file;
    wasm_file_size = sizeof(wasm_test_file);

    /* load WASM module */
    LOGI("wasm_runtime_load");
    if (!(wasm_module = wasm_runtime_load(wasm_file_buf, wasm_file_size,
                                          error_buf, sizeof(error_buf)))) {
        LOGI("in wasm_runtime_load %s\n", error_buf);
        LOGI("goto fail1\n");
        goto fail1;
    }

    /* instantiate the module */
    LOGI("wasm_runtime_instantiate");
    if (!(wasm_module_inst =
              wasm_runtime_instantiate(wasm_module, 64 * 1024, /* stack size */
                                       64 * 1024,              /* heap size */
                                       error_buf, sizeof(error_buf)))) {
        LOGI("%s\n", error_buf);
        LOGI("goto fail2\n");
        goto fail2;
    }

    LOGI("run main() of the application");
    app_instance_main(wasm_module_inst);

    /* destroy the module instance */
    LOGI("wasm_runtime_deinstantiate");
    wasm_runtime_deinstantiate(wasm_module_inst);

fail2:
    /* unload the module */
    LOGI("wasm_runtime_unload");
    wasm_runtime_unload(wasm_module);

fail1:
    // in our case, we don't need a free, but it is not a typical one
    /* free the file buffer */
    // bh_free((void *) wasm_file_buf);

    /* destroy runtime environment */
    LOGI("wasm_runtime_destroy");
    wasm_runtime_destroy();
    return;
}
