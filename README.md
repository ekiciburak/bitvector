# bitvector
A Coq library for dependently typed bitvectors.

Many of the proofs in `BVList.v` and `InvCond.v` benefits from the
recostruction tactics of Due to [Coqhammer](https://github.com/lukaszcz/coqhammer) tool.
One does not need to install Coqhammer to compile the library, since all such tactics
are in `Reconstr.v`.

In the ~/bitvector/ directory, 
1. To make, type:
	(a) coq_makefile -f _CoqProject -o Makefile
	(b) make
2. Open DepInvCond.v in coqide using
	coqide DepInvCond.v
