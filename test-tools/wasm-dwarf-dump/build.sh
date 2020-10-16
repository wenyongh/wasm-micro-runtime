if [ ! -d "binaryen" ]; then
    echo "git pull binaryen..."
    git clone https://github.com/WebAssembly/binaryen
    [ $? -eq 0 ] || exit $?
    cd binaryen
    cp -a ../src/wasm-dwarf-dump.cpp src/tools/
    patch -p1 < ../binaryen.patch
    cd ..
fi

mkdir -p build
cd build
cmake ../binaryen
make
