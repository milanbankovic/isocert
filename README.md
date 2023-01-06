# A proof system for graph (non-)isomorphism verification
 
## Introduction

This repository contains an implementation of a _canonical labeling_
algorithm for unordered graphs, based on general scheme given by
[McKay and
Piperno](https://www.sciencedirect.com/science/article/pii/S0747717113001193).
Within this scheme, it holds that two graphs are _isomorphic_ if and
only if they have equal canonical labelings. Therefore, canonical
labelings (and the algorithm that produces them) may be exploited for
checking graph (non-)isomorphism.

However, since the McKay/Piperno's algorithm for computing canonical
labeling of a given graph is fairly complex (as well as many other
algorithms that serve for the similar purposes), it is not easily
trusted, which may be a serious drawback in some critical
applications, such as an integration within a _interactive theorem
provers_. In such cases, the algorithm should be either formally
verified (which can be a hard and tedious task), or it should be
extended to generate a _certificate_ which proves that the algorithm's
output is indeed a canonical labeling of the given graph. Such
certificate should be independently checked by another tool which is,
by assumption, much simpler than the algorithm itself, and is,
therefore, easier to trust (or to be formally verified).

As a part of this work, we have developed a _proof system_ consisting
of a set of rules describing the operations performed by the canonical
labeling algorithm. The algorithm exports the rules applied during the
search, and the obtained chain of rules forms the certificate, ending
with the rule that derives the canonical form of the given graph.

This repository also contains an implementation of a _proof checker_
which takes a graph and its corresponding certificate as inputs, and
checks whether the provided certificate is correct for the given
graph. As a convenience, the checker may also compare the derived
canonical form with the one generated by the canonical labeling
algorithm and report whether they are equal.  It is also possible to
give two graphs to the checker, together with the corresponding
certificates and to check whether two certificates are correct and
whether they derive equal canonical forms (effectively verifying the
isomorphism status of the two graphs).

## Organization of the repository

This repository contains four directories:

- morphi: this directory contains the implementation of the canonical
  labeling algorithm, extended with support for certificate
  generation, based on our proof system

- checker: this directory contains the implementation of the proof
  checker

- results: this directory contains details on experimental evaluation
  of our implementations

- thy: this directory contains a formalization (within Isabelle/HOL
  theorem prover) of the McKay/Piperno's canonical labeling scheme.
  Our proof system is also formalized and its soundness is proven. We
  also provide an abstract specification of the checker and prove its
  correctness.
  

Further details may be found in each of the subdirectories.


