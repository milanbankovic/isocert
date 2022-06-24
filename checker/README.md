# Proof checker implementation

## Introduction

The proof checker implementation consists of several files:

- common.hpp: contains some basic data structures (graphs, colorings)
  as well as functions for calculating hash functions and reading
  utf8-based binary proof format.

- checker.cpp: contains the main proof-checking loop, which reads the
  rules from the certificate one by one, checks whether the rule is
  correctly applied and stores the derived fact into the in-memory
  fact database. The last rule should derive the canonical form, which
  may be compared to the given canonical form obtained by the
  canonical labeling algorithm, if provided.

- hash_database.hpp: contains the implementation of the fact database
  using the C++ built-in unordered_set<> container template.

- trie.hpp: contains the more space efficient (but also more complex)
  implementation of the fact database, based on prefix tries.

- mem_mapper.hpp: implements the memory mapping interface (for
  UNIX-compatible systems), for efficient reading of the certificate
  file.

## Compiling the checker

The checker is easily compiled by invoking:

    make

The make tool invokes the command:

    g++ -Wall -O3 -std=c++17 -DNDEBUG -D_ENABLE_MMAP -D_PREFIX_TREE  -o checker checker.cpp

This means that trie-based implementation of the fact database and the
memory mapping facility are enabled by default. If you want to change
this, you may invoke the compiler by hand, or to change the Makefile
in the appropriate way (i.e., by dropping the command line options
-D_ENABLE_MMAP and/or -D_PREFIX_TREE). Note that C++17 (at least) is
required in order to compile the code properly.

## Using the checker

The best way to learn how to use checker is to invoke it without any
command line options:

    ./checker

This will print a help message with invocation synopsis and usage
examples:

> usage: ./checker graph_file proof_file [-h | canon_graph_file | graph2_file proof2_file]
>
> Examples: 
> 1) The command: 
>    ./checker input_graph.in proof_file.in
> checks the proof given in proof_file.in for the graph given in input_graph.in
> 2) The command: 
>    ./checker input_graph.in proof_file.in -h
> prints the proof rules from proof_file.in for the graph given in input_graph.in in a human readable form (for debugging)
> 3) The command: 
>    ./checker input_graph.in proof_file.in can_graph.in
> checks the proof given in proof_file.in for the graph given in input_graph.in, and then compares the derived canonical form with the graph given in can_graph.in
> 4) The command: 
>    ./checker input_graph1.in proof_file1.in input_graph2.in proof_file2.in
> checks the proof given in proof_file{1,2}.in for the graph given in input_graph{1,2}.in, and then compares the derived canonical forms of the two graphs

> All graphs should be given in DIMACS format

In general, it is assumed that all graphs are given in [DIMACS
format](http://lcs.ios.ac.cn/~caisw/Resource/about_DIMACS_graph_format.txt),
and that proof certificates are given in the binary format described
in the corresponding [paper](https://arxiv.org/abs/2112.14303v1).


