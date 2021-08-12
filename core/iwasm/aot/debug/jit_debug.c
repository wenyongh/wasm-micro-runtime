/*
 * Copyright (C) 2015 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * 
 * Copyright (C) 2021 Ant Group.  All rights reserved.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#include "bh_log.h"
#include "bh_platform.h"
#include "wasm_runtime.h"

#include <stdio.h>
#include <assert.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>

// This must be kept in sync with gdb/gdb/jit.h .
#ifdef __cplusplus
extern "C" {
#endif
typedef enum {
    JIT_NOACTION = 0,
    JIT_REGISTER_FN,
    JIT_UNREGISTER_FN
} JITAction;
typedef struct JITCodeEntry {
    struct JITCodeEntry *next_;
    struct JITCodeEntry *prev_;
    const uint8_t *symfile_addr_;
    uint64_t symfile_size_;
} JITCodeEntry;

typedef struct JITDescriptor {
    uint32_t version_;
    uint32_t action_flag_;
    JITCodeEntry *relevant_entry_;
    JITCodeEntry *first_entry_;
} JITDescriptor;

//LLVM has already define this.
#if (WASM_ENABLE_WAMR_COMPILER == 0) && (WASM_ENABLE_JIT == 0)
// GDB will place breakpoint into this function.
// To prevent GCC from inlining or removing it we place noinline attribute
// and inline assembler statement inside.
void __attribute__((noinline)) __jit_debug_register_code();

void __attribute__((noinline)) __jit_debug_register_code()
{
    int x;
    *(char *)&x = '\0';
}

// GDB will inspect contents of this descriptor.
// Static initialization is necessary to prevent GDB from seeing
// uninitialized descriptor.

JITDescriptor __jit_debug_descriptor = { 1, JIT_NOACTION, NULL, NULL };
#else
extern void __jit_debug_register_code();
extern JITDescriptor __jit_debug_descriptor;
#endif

// Call __jit_debug_register_code indirectly via global variable.
// This gives the debugger an easy way to inject custom code to handle the events.
void (*__jit_debug_register_code_ptr)() = __jit_debug_register_code;

#ifdef __cplusplus
}
#endif

typedef struct WASMJITDebugEngine {
    korp_mutex jit_entry_mutex;
    bh_list jit_entry_list;
} WASMJITDebugEngine;

typedef struct WASMJITEntryNode {
    struct WASMJITEntryNode *next;
    ;
    JITCodeEntry *entry;
} WASMJITEntryNode;

static WASMJITDebugEngine *jit_debug_engine;

static WASMJITDebugEngine *
wasm_jit_debug_engin_create()
{
    WASMJITDebugEngine *engine;
    if (!(engine = wasm_runtime_malloc(sizeof(WASMJITDebugEngine)))) {
        LOG_ERROR("WASM Debug Engine error: failed to allocate memory");
        return NULL;
    }
    memset(engine, 0, sizeof(WASMJITDebugEngine));
    return engine;
}

void
initial_jit_debug_engine()
{
    if (!jit_debug_engine)
        jit_debug_engine = wasm_jit_debug_engin_create();
    os_mutex_init(&jit_debug_engine->jit_entry_mutex);
    bh_list_init(&jit_debug_engine->jit_entry_list);
}

static JITCodeEntry *
CreateJITCodeEntryInternal(const uint8_t *symfile_addr, uint64_t symfile_size)
{
    JITCodeEntry *entry;

    if (!jit_debug_engine)
        return NULL;

    os_mutex_lock(&jit_debug_engine->jit_entry_mutex);
    if (!(entry = wasm_runtime_malloc(sizeof(JITCodeEntry)))) {
        LOG_ERROR("WASM JIT Debug Engine error: failed to allocate memory");
        os_mutex_unlock(&jit_debug_engine->jit_entry_mutex);
        return NULL;
    }
    entry->symfile_addr_ = symfile_addr;
    entry->symfile_size_ = symfile_size;
    entry->prev_ = NULL;

    entry->next_ = __jit_debug_descriptor.first_entry_;
    if (entry->next_ != NULL) {
        entry->next_->prev_ = entry;
    }
    __jit_debug_descriptor.first_entry_ = entry;
    __jit_debug_descriptor.relevant_entry_ = entry;

    __jit_debug_descriptor.action_flag_ = JIT_REGISTER_FN;

    (*__jit_debug_register_code_ptr)();
    os_mutex_unlock(&jit_debug_engine->jit_entry_mutex);
    return entry;
}

static void
DeleteJITCodeEntryInternal(JITCodeEntry *entry)
{
    if (!jit_debug_engine)
        return;
    os_mutex_lock(&jit_debug_engine->jit_entry_mutex);
    if(entry->prev_ != NULL) { entry->prev_->next_ = entry->next_; }
    else { __jit_debug_descriptor.first_entry_ = entry->next_; }
    if (entry->next_ != NULL) {
        entry->next_->prev_ = entry->prev_;
    }
    __jit_debug_descriptor.relevant_entry_ = entry;
    __jit_debug_descriptor.action_flag_ = JIT_UNREGISTER_FN;
    (*__jit_debug_register_code_ptr)();
    wasm_runtime_free(entry);
    os_mutex_unlock(&jit_debug_engine->jit_entry_mutex);
}

static void
test_save_symfile(const uint8_t *symfile_addr, uint64_t symfile_size)
{
    int fd;
    fd = open("test.o", O_RDWR | O_SYNC | O_CREAT, 0644);
    write(fd, symfile_addr, symfile_size);
    fsync(fd);
}
void
create_jit_code_entry(const uint8_t *symfile_addr, uint64_t symfile_size)
{
    JITCodeEntry *entry;
    WASMJITEntryNode *node;

    if (!jit_debug_engine)
        return;

    if (!(node = wasm_runtime_malloc(sizeof(WASMJITEntryNode)))) {
        LOG_ERROR("WASM JIT Debug Engine error: failed to allocate memory");
        return;
    }

    entry = CreateJITCodeEntryInternal(symfile_addr, symfile_size);

    if (!entry) {
        wasm_runtime_free(node);
        return;
    }

    test_save_symfile(symfile_addr, symfile_size);

    node->entry = entry;
    bh_list_insert(&jit_debug_engine->jit_entry_list, node);
}

void
destroy_jit_code_entry(const uint8_t *symfile_addr)
{
    WASMJITEntryNode *node;

    if (!jit_debug_engine)
        return;

    node = bh_list_first_elem(&jit_debug_engine->jit_entry_list);
    while (node) {
        WASMJITEntryNode *next_node = bh_list_elem_next(node);
        if (node->entry->symfile_addr_ == symfile_addr) {
            DeleteJITCodeEntryInternal(node->entry);
            bh_list_remove(&jit_debug_engine->jit_entry_list, node);
            wasm_runtime_free(node);
        }
        node = next_node;
    }
}
