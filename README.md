`BVList.v` is a Coq library for dependently typed bitvectors. It consists of a raw 
bit-vector type representing simply-typed bit-vectors, and a dependently-typed
bit-vector type that is generated by instantiating a functor (also defined in the 
library) with the raw bit-vector module.

`InvCond.v` consists of the proofs of the 12 equivalences and the 2 implications over raw 
bitvectors.

`DepInvCond.v` consists of the same proofs over dependently-typed bit-vectors. 

Many of the proofs in `BVList.v` and `InvCond.v` benefit from the
recostruction tactics of the [Coqhammer](https://github.com/lukaszcz/coqhammer) tool.
However, one does not need to install Coqhammer to be able to compile the library,
since all such tactics are in `Reconstr.v`.

To make:
1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`

Works with Coq8.16 with a bunch of deprecated warnings. I had to locally install coqhammer version coq8.16.