#!/bin/bash


uname="$(uname -s)"
unameM="$(uname -m)"
repoUrl="https://github.com/riscv-collab/riscv-gnu-toolchain.git"
repoTag="2024.03.01"
binFile="todo"
if [ -e $binFile ]
then
    echo "Riscv-gcc has been installed."
    echo "To uninstall riscv-gcc, use 'make uninstall-gcc'."
    exit 0
fi

echo "Downloading riscv-gcc..."
case $uname in
    Linux*)
        git clone --depth 1 --branch $repoTag $repoUrl
        ;;
    Darwin*)
        echo "Darwin not supported yet."
        exit 1
        ;;
    CYGWIN*)
        git clone --depth 1 --branch $repoTag $repoUrl
        ;;
    MINGW32*)
        echo "MINGW32 not supported yet."
        exit 1
        ;;
    MINGW64*)
        echo "MINGW64 not supported yet."
        exit 1
        ;;
    *)
        echo "UNKNOWN:$uname"
        exit 1
esac

gccFolder="riscv-gnu-toolchain"
tempSourceFolder="riscv-gnu-source"
mv $gccFolder $tempSourceFolder
mkdir $gccFolder
cd $gccFolder
mkdir "riscv64-unknown-elf"
# mkdir "riscv32-unknown-elf"
cd ..

baseDir="$(pwd)"
cd $tempSourceFolder
startTime=$(date)
echo "About to make compiler. Takes ~1.5 hours."
./configure --prefix="$baseDir/$gccFolder/riscv64-unknown-elf" --with-arch=rv64gcv --with-abi=lp64 
make
#./configure --prefix="$baseDir/$gccFolder/riscv32-unknown-elf" --with-arch=rv32gcv --with-abi=ilp32
#make
cd ..
rm -rf $tempSourceFolder
echo "Riscv-gcc has been installed. Install start time: $startTime. Finished: $(date)"
