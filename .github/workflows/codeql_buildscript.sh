#!/usr/bin/env bash

sudo apt install -y build-essential cmake g++-multilib libgcc-9-dev lib32gcc-9-dev ccache ninja-build

WAMR_DIR=${PWD}

#cd wamr-compiler
#./build_llvm.sh
#mkdir build && cd build
#cmake ..
#make
# wamrc is generated under current directory

# iwasm with default features
cd ${WAMR_DIR}/product-mini/platforms/linux
rm -fr build && mkdir build && cd build
cmake ..
make -j

# iwasm with extra features
cd ${WAMR_DIR}/product-mini/platforms/linux
rm -fr build && mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug \
    -DWAMR_BUILD_LIB_PTHREAD=1 -DWAMR_BUILD_LIB_PTHREAD_SEMAPHORE=1 \
    -DWAMR_BUILD_MULTI_MODULE=1 -DWAMR_BUILD_SIMD=1 \
    -DWAMR_BUILD_TAIL_CALL=1 -DWAMR_BUILD_REF_TYPES=1 \
    -DWAMR_BUILD_CUSTOM_NAME_SECTION=1 -DWAMR_BUILD_MEMORY_PROFILING=1 \
    -DWAMR_BUILD_PERF_PROFILING=1 -DWAMR_BUILD_DUMP_CALL_STACK=1 \
    -DWAMR_BUILD_LOAD_CUSTOM_SECTION=1
make -j

# iwasm with several seldom used features
cd ${WAMR_DIR}/product-mini/platforms/linux
rm -fr build && mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug \
    -DWAMR_BUILD_ALLOC_WITH_USER_DATA=1 \
    -DWAMR_DISABLE_STACK_HW_BOUND_CHECK=1 \
    -DWAMR_BUILD_GLOBAL_HEAP_POOL=1 \
    -DWAMR_BUILD_GLOBAL_HEAP_SIZE=131072
make -j

# iwasm with wasi-threads
cd ${WAMR_DIR}/product-mini/platforms/linux
rm -fr build && mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug -DWAMR_BUILD_LIB_WASI_THREADS=1
make -j
