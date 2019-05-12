# bitvector
A Coq library for dependently typed bitvectors.

Many of the proofs in `BVList.v` and `InvCond.v` benefit from the
recostruction tactics of the [Coqhammer](https://github.com/lukaszcz/coqhammer) tool.
However, one does not need to install Coqhammer to be able to compile the library,
since all such tactics are in `Reconstr.v`.

To make:
1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`
