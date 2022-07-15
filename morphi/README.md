# morphi

*morphi* is a graph isomorphism solver written in C++. The purpose of this
solver is to demonstrate the possibility of proof logging the calculation of
the canonical representation of a given graph, and it is intended that the
accompanying checker be used for verifying the produced proofs.

## Compilation

*morphi* can be built using the GNU Make tool, by simply running the `make`
command.

## Usage

*morphi* reads its input from the standard input stream. It accepts a DIMACS
formatted graph as the input, and produces the canonically relabeled graph to
the standard output stream in the same format. Reading from or writing to files
can be accomplished by redirecting the input or the output stream.

`./morphi < graph.in > canonical.out`

Two proof logging strategies are supported. Using the `-d` option will generate
the proof during the execution of the search algorithm.  Using the `-p` option
will generate the proof after the execution of the algorithm has concluded, by
running the search the second time while utilising the knowledge gained during
the initial execution. The main advantage of this approach over the first one
is that the produced proofs are usually shorter.

The proof is written to the `proof.out` file by default. This can be changed
using the `-o proof_file.out` option.

## Source code overview

 - algorithm_argo.h: Contains the implementation of the search and proof
 generation algorithms.

 - algorithm_selector.h: Implements an interface for executing the solver for
 the given parameters.

 - array.h, bitarray.h, matrix.h, vector.h: Implement the basic data structures
 using the custom allocator.

 - coloring.h: Implements a persistent data structure for representing graph
 colorings on a search tree path. A coloring is represented as a partitioned
 array of vertices. The level of the search tree where each parition occured is
 stored as well, making the structure persistent.

 - graph.h: Implements a data structure for representing a graph.

 - group.h: Implements a data structure for storing elements of a permutation
 group. Used for storing automorphisms discovered during the search. Each group
 element is represented by a set of disjoint cycles. The group orbit parition
 and point stabilizer sets are stored as well.

 - hash.h: Contains the definitions of the used hash functions.

 - memory.h: Implements the custom, stack-like allocator.

 - partition.h: Implements the union-find data structure for representing a set
 partition.

 - permutation.h: Implements a data structure for representing a permutation.

 - priority_queue.h: Implements a priority queue data structure equipped with a
 membership test.

 - proof.h: Defines an interface for exporting proofs.

 - utility.h, assertions.h, tests.h: Contain some utility structures and functions.
