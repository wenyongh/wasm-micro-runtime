# Copyright (C) 2019 Intel Corporation.  All rights reserved.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#

cmake_minimum_required (VERSION 2.8.3)

project (wasm-sourcemap-dump)

if (NOT CMAKE_BUILD_TYPE)
  SET(CMAKE_BUILD_TYPE Debug)
endif ()

message(${CMAKE_CURRENT_LIST_DIR})

set (CJSON_DIR ${CMAKE_CURRENT_LIST_DIR}/../../test-tools/host-tool/external/cJSON)

include (${CJSON_DIR}/cjson.cmake)

set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -Wformat \
                                     -Wformat-security -Wno-pointer-sign")

SET(SOURCES ${CJSON_SOURCE} src/main.c)
    
add_executable(wasm-sourcemap-dump ${SOURCES})

