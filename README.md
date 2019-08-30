# Clang Static  Analyzer Pluging for interger overflow detection
UWAGA!!! **Project in process** (not finished/may cause discausting).

**Created during the internship "Summ3r 0f h4ck 2019" in Digital Security.**

### What it can do now?
    - CSA plugin skeleton
    - Detect potentional IO
    - Base for taint analysis (based on GenericTaintChecker.cpp)

### Future work:
    - Replace implemention of taint class
    - Add SMT solvers or some math approach

### How to build
    1. Put code in /llvm/source/path/clang/lib/StaticAnalyzer/Checkers
    2. cd in clang build directory
    3. make clangStaticAnalyzerCheckers
    Why this way? It's temperary solution.

### How to run
clang++ -cc1 -o report/dir/path -x c++ -load ../lib/path/pluginlib.so -analyze -analyzer-checker=test.Me -analyzer-config test.Me:ParamName=ParamVal  YourPlugn.cpp

### Now it looks like this
 ![](https://raw.githubusercontent.com/dR3m/IntOverflow-CSA-plugin/master/imgs/1.jpg "Test source code")
 ![](https://raw.githubusercontent.com/dR3m/IntOverflow-CSA-plugin/master/imgs/2.jpg "Test checker result")
