# Symbolic Execution Application

This program symbolically explores all program paths using the EXE algorith in a .prg file. All .prg files use the imperative language WHILE.

EXE symbolic execution steps:

- Execute program using symbolic input values
- Fork execution at each decision
- Record branching conditions
- Can be use to analyse program behaviour using symbolic values

The implementation of the symbolic execution engine is located in directory wlang. Execute the app using the following command inside a virtual environment that uses python 2 and has z3 installed:


`(venv) $ python -m wlang.sym wlang/test1.prg`


Get z3 from the link below:

https://github.com/Z3Prover/z3

