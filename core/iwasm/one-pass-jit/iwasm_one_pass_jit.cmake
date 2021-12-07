# Copyright (C) 2019 Intel Corporation.  All rights reserved.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

set (IWASM_ONE_PASS_JIT_DIR ${CMAKE_CURRENT_LIST_DIR})

add_definitions (-DWASM_ENABLE_ONE_PASS_JIT=1)

include_directories (${IWASM_ONE_PASS_JIT_DIR})

file (GLOB c_source_all ${IWASM_ONE_PASS_JIT_DIR}/*.c)

set (IWASM_ONE_PASS_JIT_SOURCE ${c_source_all})
