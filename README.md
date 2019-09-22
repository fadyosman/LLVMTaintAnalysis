# LLVMTaintAnalysis
An llvm pass to perform taint analysis on your code.

# Compilation
```
mkdir build
cd build
cmake ../
make
```


# Usage
Using the opt tool:
```
opt -load=libLLVMTaintAnalysis.so -instnamer -taintanalyzer < code_to_scan.ll
```
