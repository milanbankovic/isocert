# False proofs

This is a collection of patch files which introduce various bugs into
the solver. Patches may be applied using the `patch` command.

`patch algorithm_argo.h path/to/bug.patch`

After introducing a bug, *morphi* can be compiled as usual. Ideally,
running the solver will produce an incorrect proof which should be
rejected by the checker, but a valid proof may be produced instead,
depending on the bug and on the input graph.

## List of bugs

 - eager\_backjump: Allows backjumping when it would lead to incorrect
   pruning of the search tree.

 - faulty\_invariant\_comparison: Allows incorrect assumptions when
   incrementally comparing node invariants lexicographically.

 - incomplete\_cell: Excludes the first vertex of the target cell from
   tree traversal.

 - incorrect\_invariant: Excludes some edges of the quotient graph
   from invariant calculation.

 - missing\_vertex: Removes all adjacencies from vertex 0 during the
   general refinement procedure.

 - no\_invariant\_decrement: Removes the decrement part of invariant
   calculation.

 - no\_rotate: Removes the cell rotation part of the refinement
   procedure.

 - unnecessary\_facts: Outputs additional facts when traversing a
   pruned subtree for automorphism discovery.
