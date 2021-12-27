#ifndef ALGORITHM_DFS_H
#define ALGORITHM_DFS_H

#include <cstdint>
#include <limits>
#include <numeric>
#include "vector.h"
#include "matrix.h"
#include "bitarray.h"
#include "coloring.h"
#include "graph.h"
#include "hash.h"
#include "partition.h"
#include "group.h"
#include "assertions.h"
#include "priority_queue.h"
#include "proof.h"

namespace morphi {

template<typename T, typename HashType>
class AlgorithmDFS {
public:

    enum PathType {
        MaxPath = 1,
        AutPath = 2,
    };

    struct NodePath {
        NodePath(size_t size) : permutation(size), coloring(size), invariants(size), stabilized(size) {}

        bool is_leaf = false;
        T lca_level = 0;
        Permutation<T> permutation;
        Coloring<T> coloring;
        Vector<HashType> invariants;
        Vector<T> stabilized;
    };

    AlgorithmDFS(size_t vertices, size_t edges, Array<uint32_t>& edge_list, Array<uint32_t>& colors, size_t aut_limit, std::string proof_file)
        : graph(vertices, edges, edge_list.m_data),
          input_coloring(vertices),
          coloring(vertices, colors.m_data),
          invariants(vertices + 1),
          stabilized(vertices),
          max_node(vertices),
          fst_node(vertices),
          automorphisms(vertices, aut_limit),
          quotient_graph(vertices),
          proof(proof_file)
    {
        input_coloring.copy(coloring);
    }

    void generateProof() {
        coloring.copy(input_coloring);
        proof.open();
        proof.coloringAxiom();
        Vector<T> target_cells(2 * max_node.stabilized.m_size * coloring.size());
        prove(true, target_cells);
        proof.pathAxiom();
        size_t target_idx = 0;
        for(size_t idx = 0; idx < max_node.stabilized.m_size; idx++) {
            Vector<T> cell_content(coloring.size());
            while(target_cells[target_idx] != coloring.size())
                cell_content.push(target_cells[target_idx++]);
            target_idx++;
            proof.extendPath(idx, max_node.stabilized, cell_content, max_node.stabilized[idx]);
        }
        proof.canonicalLeaf(max_node.stabilized, max_node.permutation.m_forward);
        proof.close();
        std::cerr << "Proof size: " << statistics.proof_size << std::endl;
    }

    // returns whether the whole subtree has been pruned
    bool prove(bool canon_path, Vector<T>& target_cells) {
        statistics.proof_size++;

        T level = stabilized.m_size;
        refine(true);

        proof.invariantAxiom(stabilized);

        assert(invariants.back() <= max_node.invariants[level]);

        if(invariants.back() != max_node.invariants[level]) {
            proof.pruneInvariant(level, max_node.stabilized, max_node.coloring, stabilized, coloring);
            unrefine();
            return true;
        }

        if(stabilized.m_size > 0) {
            canon_path = canon_path && stabilized.back() == max_node.stabilized[level - 1];
            proof.invariantsEqual(level, max_node.stabilized, max_node.coloring, stabilized, coloring);
        }

        size_t cell_idx;
        Array<T> cell_content = targetCell(cell_idx);

        if(canon_path && cell_content.m_size > 0) {
            for(auto ptr = cell_content.m_data; ptr != cell_content.m_end; ptr++)
                target_cells.push(*ptr);
            target_cells.push(coloring.size());
        }

        if(cell_content.m_size > 0)
            proof.targetCell(stabilized, coloring);

        Partition<T> orbit_partition(coloring.size());
        size_t aut_counter = 0;

        BitArray axiom_written(coloring.size());

        size_t pruned_count = 0;

        if(canon_path && cell_content.m_size > 0) {
            individualize(cell_idx, max_node.stabilized[level], true);
            pruned_count += prove(canon_path, target_cells);
            unindividualize(cell_idx);
        }

        for(auto ptr = cell_content.m_data; ptr != cell_content.m_end; ptr++) {
            if(canon_path && *ptr == max_node.stabilized[level])
                continue;

            auto onMerge = [&](size_t aut_idx, T vertex1, T vertex2) {
                if(!axiom_written[vertex1]) {
                    proof.orbitsAxiom(vertex1, stabilized);
                    axiom_written.set(vertex1);
                }
                if(!axiom_written[vertex2]) {
                    proof.orbitsAxiom(vertex2, stabilized);
                    axiom_written.set(vertex2);
                }
                T p1 = orbit_partition.mcr(vertex1);
                T p2 = orbit_partition.mcr(vertex2);
                if(p1 != p2) {
                    Vector<T> orbit1(coloring.size());
                    Vector<T> orbit2(coloring.size());
                    for(size_t idx = 0; idx < coloring.size(); idx++) {
                        T p = orbit_partition.mcr(idx);
                        if(p == p1)
                            orbit1.push(idx);
                        else if(p == p2)
                            orbit2.push(idx);
                    }
                    Array<T> automorphism(coloring.size());
                    std::iota(automorphism.m_data, automorphism.m_end, 0);
                    // formiraj automorfizam na osnovu aut_idx
                    auto ptr = automorphisms.elemCyclesBegin(aut_idx);
                    auto end = automorphisms.elemCyclesEnd(aut_idx);
                    T cycle_rep = automorphisms.m_points;
                    while(ptr != end) {
                        if(cycle_rep == automorphisms.m_points)
                            cycle_rep = *ptr;
                        else if(*ptr == automorphisms.m_points) {
                            automorphism[*(ptr - 1)] = cycle_rep;
                            cycle_rep = *ptr;
                        }
                        else
                            automorphism[*(ptr - 1)] = *ptr;
                        ptr++;
                    }
                    proof.mergeOrbits(orbit1, orbit2, stabilized, automorphism, vertex1, vertex2);
                }
            };
            automorphisms.updatePartitionCaller(stabilized, orbit_partition, aut_counter, onMerge);
            T p = orbit_partition.mcr(*ptr);
            if(p != *ptr) {
                Vector<T> orbit(cell_content.m_size);
                for(size_t idx = 0; idx < coloring.size(); idx++)
                    if(orbit_partition.mcr(idx) == p)
                        orbit.push(idx);
                proof.pruneOrbits(orbit, stabilized, p, *ptr);
                pruned_count++;
                continue;
            }

            individualize(cell_idx, *ptr, true);
            pruned_count += prove(canon_path, target_cells);
            unindividualize(cell_idx);
        }

        if(cell_content.m_size > 0) {
            if(canon_path)
                assert(pruned_count == cell_content.m_size - 1);
            else
                assert(pruned_count == cell_content.m_size);
        }

        if(cell_content.m_size > 0 && pruned_count == cell_content.m_size) {
            proof.pruneParent(stabilized, cell_content);
            unrefine();
            return true;
        }

        if(cell_content.m_size == 0 && !canon_path) {
            proof.pruneLeaf(level, max_node.stabilized, max_node.coloring, stabilized, coloring);
            unrefine();
            return true;
        }

        unrefine();
        return false;
    }

    const Permutation<T>& solve() {
        solve(PathType::MaxPath | PathType::AutPath);
        std::cerr << "Tree size: " << statistics.tree_size << std::endl;
        std::cerr << "Bad nodes: " << statistics.bad_nodes << std::endl;
        std::cerr << "Aut size: " << automorphisms.m_elements << std::endl;
        std::cerr << "Orbit prunes: " << statistics.orbit_prunes << std::endl;
        std::cerr << "Max path nodes: " << statistics.max_nodes << std::endl;
        std::cerr << "Aut path nodes: " << statistics.aut_nodes << std::endl;
        std::cerr << "Max path length: " << max_node.invariants.m_size << std::endl;
        std::cerr << "Fst path length: " << fst_node.invariants.m_size << std::endl;
        return max_node.permutation;
    }

    T solve(uint8_t flags) {
        statistics.tree_size++;

        assert(invariants.m_size <= stabilized.m_size);
        T level = stabilized.m_size;
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * level, ' ') << "I " << coloring << std::endl;
#endif
        refine();
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * level, ' ') << "R " << coloring << std::endl;
        std::cerr << std::string(2 * level, ' ') << (size_t) invariants.back() << std::endl;
#endif
        /*
        if(!refine()) // zameniti sa refine() == BAD_PATH
            return level;
        */

        // update max_path, aut_path nodes
        if(!fst_node.is_leaf)
            fst_node.invariants.push(invariants.back());

        bool max_path = (bool)(flags & PathType::MaxPath) &&
                         (max_node.invariants.m_size <= level ||
                          invariants.back() >= max_node.invariants[level]);
        bool aut_path = (bool)(flags & PathType::AutPath) &&
                        fst_node.invariants.m_size > level &&
                        invariants.back() == fst_node.invariants[level];

        if(max_path)
            statistics.max_nodes++;
        if(aut_path)
            statistics.aut_nodes++;
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * level, ' ');
        if(max_path) std::cerr << "MAX ";
        if(aut_path) std::cerr << "AUT ";
        if(!max_path && !aut_path) std::cerr << "BAD ";
        std::cerr << std::endl;
#endif

        if(!max_path && !aut_path) {
            statistics.bad_nodes++;
            unrefine();
            return level;
        }
        if(max_path) {
            max_node.lca_level = level;

            if(max_node.invariants.m_size > level && invariants.back() > max_node.invariants[level])
                max_node.invariants.pop(level);

            if(max_node.invariants.m_size <= level) {
                max_node.invariants.push(invariants.back());
                max_node.is_leaf = false;
            }
        }

        flags = 0;
        flags |= max_path ? PathType::MaxPath : 0;
        flags |= aut_path ? PathType::AutPath : 0;

        size_t cell_idx;
        Array<T> cell_content = targetCell(cell_idx);
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * level, ' ') << "Target cell: ";
        for(auto ptr = cell_content.m_data; ptr != cell_content.m_end; ptr++)
            std::cerr << (size_t) *ptr << ' ';
        std::cerr << std::endl;
#endif
        Partition<T> orbit_partition(coloring.size());
        size_t aut_counter = 0;
        for(auto ptr = cell_content.m_data; ptr != cell_content.m_end; ptr++) {
            if(ptr > cell_content.m_data) {
                if(level != fst_node.lca_level) {
                    automorphisms.updatePartition(stabilized, orbit_partition, aut_counter);
                    if(orbit_partition.mcr(*ptr) != *ptr) {
                        statistics.orbit_prunes++;
                        continue;
                    }
                }
                else if(automorphisms.m_orbit_partition.mcr(*ptr) != *ptr) {
                    statistics.orbit_prunes++;
                    continue;
                }
            }

            individualize(cell_idx, *ptr);
            T backjump = solve(flags);
            unindividualize(cell_idx);

            if(level > backjump) {
                unrefine();
                return backjump;
            }

            fst_node.lca_level = std::min(fst_node.lca_level, level);
            max_node.lca_level = std::min(max_node.lca_level, level);
        }

        if(cell_content.m_size == 0) {
            if(max_path && (!max_node.is_leaf || (max_node.invariants.m_size == (size_t) level + 1 && graph.less(max_node.permutation.m_inverse, coloring.m_permutation.m_forward)))) {
                max_node.is_leaf = true;
                max_node.lca_level = level;
                max_node.permutation.copyInv(coloring.m_permutation);

                max_node.stabilized.copy(stabilized);
                max_node.coloring.copy(coloring);
            }

            if(!fst_node.is_leaf) {
                fst_node.is_leaf = true;
                fst_node.lca_level = level;
                fst_node.permutation.copyInv(coloring.m_permutation);
            }

#ifdef DEBUG_NO_AUT
            unrefine();
            return level;
#endif

            //if(fst_node.lca_level != level) {
                Array<T> leaf_quotient(coloring.size());
                for(size_t idx = 0; idx < leaf_quotient.m_size; idx++)
                    //leaf_quotient[idx] = fst_node.permutation.m_inverse[coloring.m_permutation.m_inverse[idx]];
                    leaf_quotient[idx] = coloring.m_permutation.m_forward[fst_node.permutation.m_forward[idx]];

                if(graph.isAutomorphism(leaf_quotient)) {
                    automorphisms.push(leaf_quotient);
                    unrefine();
                    return fst_node.lca_level;
                }
            //}

            //if(max_node.lca_level != level) {
                //Array<T> leaf_quotient(coloring.size());
                for(size_t idx = 0; idx < leaf_quotient.m_size; idx++)
                    //leaf_quotient[idx] = max_node.permutation.m_inverse[coloring.m_permutation.m_inverse[idx]];
                    leaf_quotient[idx] = coloring.m_permutation.m_forward[max_node.permutation.m_forward[idx]];

                if(graph.isAutomorphism(leaf_quotient)) {
                    automorphisms.push(leaf_quotient);
                    unrefine();
                    return automorphisms.m_orbit_partition.mcr(stabilized[fst_node.lca_level]) != stabilized[fst_node.lca_level] ? fst_node.lca_level : max_node.lca_level;
                }
            //}
        }

        unrefine();
        return level;
    }

    void individualize(size_t cell_idx, T vertex, bool proving = false) {
        assert(coloring.m_cell_end[cell_idx] - cell_idx > 1);
        if(proving)
            proof.individualize(stabilized, vertex, coloring);

        stabilized.push(vertex);

        T vertex_idx = coloring.m_permutation.m_inverse[vertex];
        coloring.m_permutation.swap(cell_idx, vertex_idx);

        coloring.m_cell_end[cell_idx + 1] = coloring.m_cell_end[cell_idx];
        coloring.m_cell_end[cell_idx] = cell_idx + 1;

        coloring.m_cell_level[cell_idx + 1] = stabilized.m_size;
    }

    void unindividualize(size_t cell_idx) {
        stabilized.pop();

        coloring.m_cell_end[cell_idx] = coloring.m_cell_end[cell_idx + 1];
    }

    template<typename ActiveSet, bool RootLevel, bool RotateCells>
    void refine1(size_t work_cell, ActiveSet& active_cells, HashType& invariant) {
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * stabilized.m_size, ' ') << "refine1" << std::endl;
#endif
        if constexpr (!RootLevel)
            hash::sequential32u(invariant, work_cell);

        size_t cell_beg = 0, cell_end = coloring.m_cell_end[0];
        size_t split = 0; // [cell_beg, split), [split, idx)
        for(size_t idx = 0; idx < coloring.size(); idx++) {
            if(!graph.adjacent(coloring[idx], coloring[work_cell]))
                coloring.m_permutation.swap(idx, split++);

            if(idx == cell_end - 1) {
                if(split != cell_beg && split != cell_end) {
                    coloring.m_cell_end[cell_beg] = split;
                    coloring.m_cell_end[split] = cell_end;
                    coloring.m_cell_level[split] = stabilized.m_size;

                    if constexpr (RotateCells) {
                        if(split - cell_beg >= cell_end - split) {
                            coloring.rotate(cell_beg, cell_end, stabilized.m_size);
                            split = coloring.m_cell_end[cell_beg];
                        }

                        if(active_cells.contains(cell_beg))
                            active_cells.push(split);
                        else
                            active_cells.push(cell_beg);
                    }
                    else {
                        if(active_cells.contains(cell_beg) || split - cell_beg >= cell_end - split)
                            active_cells.push(split);
                        else
                            active_cells.push(cell_beg);

                        if constexpr (!RootLevel) {
                            hash::sequential32u(invariant, cell_beg);
                            hash::sequential32u(invariant, 0);
                            hash::sequential32u(invariant, split);
                            hash::sequential32u(invariant, 1);
                        }
                    }
                }
                else if constexpr (!RootLevel) {
                    hash::sequential32u(invariant, cell_beg);
                    if(split == cell_end)
                        hash::sequential32u(invariant, 0);
                    if(split == cell_beg)
                        hash::sequential32u(invariant, 1);
                }

                if(cell_end < coloring.size()) {
                    cell_beg = split = cell_end;
                    cell_end = coloring.m_cell_end[idx + 1];
                }
            }
        }
#ifdef DEBUG_SLOW_ASSERTS
        assertValidColoring(coloring);
#endif
    }

    template<typename ActiveSet, bool RootLevel, bool RotateCells>
    void refine2(size_t work_cell, ActiveSet& active_cells, HashType& invariant) {
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * stabilized.m_size, ' ') << "refine2" << std::endl;
#endif
        if constexpr (!RootLevel)
            hash::sequential32u(invariant, work_cell);

        size_t cell_beg = 0, cell_end = coloring.m_cell_end[0];
        size_t split1 = 0, split2 = cell_end; // [cell_beg, split1), [split1, idx), [split2, cell_end)
        size_t idx = 0;
        while(idx < coloring.size()) {
            assert(cell_beg <= split1);
            assert(split1 <= idx);
            assert(idx <= split2);
            assert(split2 <= cell_end);
            uint8_t adj_count = (uint8_t) graph.adjacent(coloring[idx], coloring[work_cell]) +
                                (uint8_t) graph.adjacent(coloring[idx], coloring[work_cell + 1]);
            if(adj_count == 0)
                coloring.m_permutation.swap(idx++, split1++);
            else if(adj_count == 1)
                idx++;
            else
                coloring.m_permutation.swap(idx, --split2);

            if(idx == split2) {
                if(cell_beg != split1 && split1 != split2 && split2 != cell_end) {
                    coloring.m_cell_end[cell_beg] = split1;
                    coloring.m_cell_end[split1] = split2;
                    coloring.m_cell_level[split1] = stabilized.m_size;
                    coloring.m_cell_end[split2] = cell_end;
                    coloring.m_cell_level[split2] = stabilized.m_size;

                    if constexpr (RotateCells) {
                        if(split1 - cell_beg >= split2 - split1 && split1 - cell_beg >= cell_end - split2) {
                            coloring.rotate(cell_beg, cell_end, stabilized.m_size);
                            split1 = coloring.m_cell_end[cell_beg];
                            split2 = coloring.m_cell_end[split1];
                        }
                        else if(split2 - split1 >= cell_end - split2) {
                            coloring.rotate(split1, cell_end, stabilized.m_size);
                            split2 = coloring.m_cell_end[split1];
                        }

                        if(active_cells.contains(cell_beg)) {
                            active_cells.push(split1);
                            active_cells.push(split2);
                        }
                        else {
                            active_cells.push(cell_beg);
                            active_cells.push(split1);
                        }
                    }
                    else {
                        if(active_cells.contains(cell_beg) || (split1 - cell_beg >= split2 - split1 && split1 - cell_beg >= cell_end - split2)) {
                            active_cells.push(split1);
                            active_cells.push(split2);
                        }
                        else if(split2 - split1 >= cell_end - split2) {
                            active_cells.push(cell_beg);
                            active_cells.push(split2);
                        }
                        else {
                            active_cells.push(cell_beg);
                            active_cells.push(split1);
                        }

                        if constexpr (!RootLevel) {
                            hash::sequential32u(invariant, cell_beg);
                            hash::sequential32u(invariant, 0);
                            hash::sequential32u(invariant, split1);
                            hash::sequential32u(invariant, 1);
                            hash::sequential32u(invariant, split2);
                            hash::sequential32u(invariant, 2);
                        }
                    }
                }
                else if((cell_beg != split1 && split1 != split2) ||
                        (split1 != split2 && split2 != cell_end) ||
                        (cell_beg != split1 && split2 != cell_end)) {
                    size_t split = split1 != cell_beg ? split1 : split2;

                    coloring.m_cell_end[cell_beg] = split;
                    coloring.m_cell_end[split] = cell_end;
                    coloring.m_cell_level[split] = stabilized.m_size;

                    if constexpr(RotateCells) {
                        if(split - cell_beg >= cell_end - split) {
                            coloring.rotate(cell_beg, cell_end, stabilized.m_size);
                            split = coloring.m_cell_end[cell_beg];
                        }

                        if(active_cells.contains(cell_beg))
                            active_cells.push(split);
                        else
                            active_cells.push(cell_beg);
                    }
                    else {
                        if(active_cells.contains(cell_beg) || split - cell_beg >= cell_end - split)
                            active_cells.push(split);
                        else
                            active_cells.push(cell_beg);

                        if constexpr (!RootLevel) {
                            if(cell_beg != split1) {
                                hash::sequential32u(invariant, cell_beg);
                                hash::sequential32u(invariant, 0);
                            }
                            if(split1 != split2) {
                                hash::sequential32u(invariant, split1);
                                hash::sequential32u(invariant, 1);
                            }
                            if(split2 != cell_end) {
                                hash::sequential32u(invariant, split2);
                                hash::sequential32u(invariant, 2);
                            }
                        }
                    }
                }
                else if constexpr (!RootLevel) {
                    hash::sequential32u(invariant, cell_beg);
                    if(split1 == cell_end)
                        hash::sequential32u(invariant, 0);
                    if(split1 == cell_beg && split2 == cell_end)
                        hash::sequential32u(invariant, 1);
                    if(split2 == cell_beg)
                        hash::sequential32u(invariant, 2);
                }

                if(cell_end < coloring.size()) {
                    idx = cell_beg = split1 = cell_end;
                    cell_end = split2 = coloring.m_cell_end[idx];
                }
                else break;
            }
        }
#ifdef DEBUG_SLOW_ASSERTS
        assertValidColoring(coloring);
#endif
    }

    template<typename ActiveSet, bool RootLevel, bool RotateCells>
    void refineN(size_t work_cell, ActiveSet& active_cells, HashType& invariant) {
#ifdef DEBUG_OUT
        std::cerr << std::string(2 * stabilized.m_size, ' ') << "refineN" << std::endl;
#endif

#ifdef QT_QML_DEBUG
        Array<T> tmp(coloring.size());
        for(size_t cell = 0; cell < coloring.size(); cell = coloring.m_cell_end[cell])
            for(size_t idx = cell; idx < coloring.m_cell_end[cell]; idx++)
                tmp[coloring[idx]] = cell;
#endif

        Array<T> adj_count(coloring.size(), 0);

        size_t work_end = coloring.m_cell_end[work_cell];
        for(size_t idx = work_cell; idx != work_end; idx++) {
            T vertex = coloring[idx];
            for(auto ptr = graph.begin(vertex); ptr != graph.end(vertex); ptr++)
                adj_count[*ptr]++;
        }

        Array<T> buckets(coloring.size(), 0);
        for(auto ptr = adj_count.m_data; ptr != adj_count.m_end; ptr++)
            buckets[*ptr]++;

        for(auto ptr = buckets.m_data + 1; ptr != buckets.m_end; ptr++)
            *ptr += *(ptr - 1);

        struct VertexCell { T vertex; T cell; };
        Array<VertexCell> sorted(coloring.size());
        Array<T> cell_buckets(coloring.size());
        size_t cell_beg = 0, cell_end = coloring.m_cell_end[0];
        for(size_t idx = 0; idx < coloring.size(); idx++) {
            T vertex = coloring[idx];
            sorted[--buckets[adj_count[vertex]]] = {.vertex = vertex, .cell = (T) cell_beg};
            if(idx == cell_end - 1) {
                cell_buckets[cell_beg] = cell_end;
                cell_beg = cell_end;
                if(cell_beg < coloring.size()) cell_end = coloring.m_cell_end[cell_beg];
            }
        }

        for(size_t idx = coloring.size(); idx != 0; idx--) {
            VertexCell& vertex = sorted[idx - 1];
            coloring.m_permutation.set(--cell_buckets[vertex.cell], vertex.vertex);
        }

        /*Array<T> sorted(coloring.size());
        std::copy(coloring.m_permutation.m_forward.m_data, coloring.m_permutation.m_forward.m_end, sorted.m_data);
        for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx])
            std::sort(sorted.m_data + cell_idx, sorted.m_data + coloring.m_cell_end[cell_idx], [&adj_count](T a, T b) { return adj_count[a] == adj_count[b] ? a < b : adj_count[a] < adj_count[b]; });
        for(size_t idx = 0; idx < coloring.size(); idx++)
            coloring.m_permutation.set(idx, sorted[idx]);
        size_t cell_beg, cell_end;*/

#ifdef QT_QML_DEBUG
        for(size_t cell = 0; cell < coloring.size(); cell = coloring.m_cell_end[cell]) {
            for(size_t idx = cell; idx < coloring.m_cell_end[cell]; idx++)
                assert(tmp[coloring[idx]] == cell);
            for(size_t idx = cell + 1; idx < coloring.m_cell_end[cell]; idx++)
                assert(adj_count[coloring[idx - 1]] <= adj_count[coloring[idx]]);
        }
#endif

        if constexpr (!RootLevel)
            hash::sequential32u(invariant, work_cell);

        size_t cell_prev, max_cell;
        for(cell_beg = 0; cell_beg != coloring.size(); cell_beg = cell_end) {
            cell_end = coloring.m_cell_end[cell_beg];
            assert(cell_end > cell_beg);
            cell_prev = cell_beg;

            if constexpr (RotateCells) {
                max_cell = cell_beg;
                for(size_t idx = cell_beg + 1; idx != cell_end; idx++) {
                    if(adj_count[coloring[idx]] != adj_count[coloring[idx - 1]]) {
                        coloring.m_cell_end[cell_prev] = idx;
                        coloring.m_cell_end[idx] = cell_end;
                        coloring.m_cell_level[idx] = stabilized.m_size;

                        if(coloring.cellSize(cell_prev) > coloring.cellSize(max_cell))
                            max_cell = cell_prev;
                        cell_prev = idx;
                        assert(cell_prev < coloring.size());
                    }
                }
                if(coloring.cellSize(cell_prev) > coloring.cellSize(max_cell))
                    max_cell = cell_prev;

                coloring.rotate(max_cell, cell_end, stabilized.m_size);

                if(active_cells.contains(cell_beg))
                    for(size_t cell_idx = coloring.m_cell_end[cell_beg]; cell_idx != cell_end; cell_idx = coloring.m_cell_end[cell_idx])
                        active_cells.push(cell_idx);
                else
                    for(size_t cell_idx = cell_beg; coloring.m_cell_end[cell_idx] != cell_end; cell_idx = coloring.m_cell_end[cell_idx])
                        active_cells.push(cell_idx);
            }
            else {
                if constexpr(!RootLevel) {
                    hash::sequential32u(invariant, cell_beg);
                    hash::sequential32u(invariant, adj_count[coloring[cell_beg]]);
                }

                if(active_cells.contains(cell_beg)) {
                    for(size_t idx = cell_beg + 1; idx != cell_end; idx++)
                        if(adj_count[coloring[idx]] != adj_count[coloring[idx - 1]]) {
                            coloring.m_cell_end[cell_prev] = idx;
                            coloring.m_cell_end[idx] = cell_end;
                            coloring.m_cell_level[idx] = stabilized.m_size;
                            if constexpr(!RootLevel) {
                                hash::sequential32u(invariant, idx);
                                hash::sequential32u(invariant, adj_count[coloring[idx]]);
                            }
                            cell_prev = idx;
                            assert(cell_prev < coloring.size());

                            active_cells.push(idx);
                        }
                }
                else {
                    max_cell = cell_beg;
                    for(size_t idx = cell_beg + 1; idx != cell_end; idx++) {
                        if(adj_count[coloring[idx]] != adj_count[coloring[idx - 1]]) {
                            coloring.m_cell_end[cell_prev] = idx;
                            coloring.m_cell_end[idx] = cell_end;
                            coloring.m_cell_level[idx] = stabilized.m_size;
                            if constexpr(!RootLevel) {
                                hash::sequential32u(invariant, idx);
                                hash::sequential32u(invariant, adj_count[coloring[idx]]);
                            }

                            if(coloring.cellSize(cell_prev) > coloring.cellSize(max_cell))
                                max_cell = cell_prev;
                            cell_prev = idx;
                            assert(cell_prev < coloring.size());
                        }
                    }
                    if(coloring.cellSize(cell_prev) > coloring.cellSize(max_cell))
                        max_cell = cell_prev;

                    for(size_t cell_idx = cell_beg; cell_idx != cell_end; cell_idx = coloring.m_cell_end[cell_idx])
                        if(cell_idx != max_cell)
                            active_cells.push(cell_idx);
                }
            }
#ifdef DEBUG_SLOW_ASSERTS
            assertCellSplittingValid(coloring, cell_beg, cell_end, adj_count, stabilized.m_size);
#endif
        }

#ifdef DEBUG_SLOW_ASSERTS
        assertValidColoring(coloring);
#endif
    }

    template<typename ActiveSet>
    void refineCells(size_t work_cell, size_t work_size, ActiveSet& active_cells, HashType& invariant) {
        //if(stabilized.m_size == 0) {
            if(work_size == 1)
                refine1<ActiveSet, true, true>(work_cell, active_cells, invariant);
            else if(work_size == 2)
                refine2<ActiveSet, true, true>(work_cell, active_cells, invariant);
            else
                refineN<ActiveSet, true, true>(work_cell, active_cells, invariant);
        /*}
        else {
            if(work_size == 1)
                refine1<false>(work_cell, active_cells, invariant);
            else if(work_size == 2)
                refine2<false>(work_cell, active_cells, invariant);
            else
                refineN<false>(work_cell, active_cells, invariant);
        }*/
    }

    void refine(bool proving = false) {
        PriorityQueue<T> active_cells(coloring.size());
        //Vector<T> active_cells(coloring.size());
        //BitArray is_active(coloring.size());

        if(stabilized.m_size > 0) {
            T cell_idx = coloring.m_permutation.m_inverse[stabilized.back()];
            active_cells.push(cell_idx);
            //is_active.set(cell_idx);
            assert(coloring.m_cell_end[cell_idx] != 0);
        }
        else {
            for(size_t cell_idx = 0; cell_idx != coloring.size(); cell_idx = coloring.m_cell_end[cell_idx]) {
                active_cells.push(cell_idx);
                //is_active.set(cell_idx);
                assert(coloring.m_cell_end[cell_idx] != 0);
            }
        }

        HashType invariant = 0;
        while(active_cells.m_size > 0) {
            /*size_t work_cell = active_cells.back();
            active_cells.pop();
            is_active.clear(work_cell);*/
            size_t work_cell = active_cells.pop();

            assert(coloring.m_cell_end[work_cell] != 0);

            // For proof only
            size_t cells = 0;
            Coloring<T> prev_coloring(coloring.size());
            prev_coloring.copy(coloring);
            if(proving) {
                for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx])
                    cells++;
            }

            size_t work_size = coloring.m_cell_end[work_cell] - work_cell;
            refineCells(work_cell, work_size, active_cells, invariant);

            // For proof only
            if(proving) {
                size_t cells_after = 0;
                for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx])
                    cells_after++;
                if(cells_after != cells)
                    proof.splitColoring(stabilized, prev_coloring);
            }

#ifdef DEBUG_SLOW_ASSERTS
            assertColoringSplittingValid(coloring, graph, work_cell, work_size);
#endif

            size_t cell_idx = 0;
            while(coloring.cellSize(cell_idx) == 1)
                cell_idx++;
            if(cell_idx == coloring.size())
                break;

#ifdef DEBUG_OUT
            std::cerr << std::string(2 * stabilized.m_size, ' ') << coloring << " : " << work_cell << std::endl;
#endif
        }
        if(proving)
            proof.equitable(stabilized, coloring);

#ifdef DEBUG_SLOW_ASSERTS
        assertEquitableColoring(coloring, graph);
#endif
        invariant = calculateQuotientInvariantIncrement();
        //invariant = calculateMultisetQuotientInvariant();
        invariants.push(invariant);
    }

    HashType calculateQuotientInvariant() {
        HashType invariant = 0;
        if(stabilized.m_size == 0)
            return invariant;
        for(size_t cell = 0; cell < coloring.size(); cell = coloring.m_cell_end[cell]) {
            hash::sequential32u(invariant, cell);
            hash::sequential32u(invariant, coloring.cellSize(cell));
            for(size_t oth_cell = 0; oth_cell < coloring.size(); oth_cell = coloring.m_cell_end[oth_cell]) {
                T adj_count = 0;
                for(size_t idx = cell; idx < coloring.m_cell_end[cell]; idx++)
                    adj_count += graph.adjacent(coloring.m_permutation[oth_cell], coloring.m_permutation[idx]);
                hash::sequential32u(invariant, adj_count);
            }
        }
        return invariant;
    }

    HashType calculateMorphiInvariant() {
        HashType invariant = 0;
        if(stabilized.m_size == 0)
            return invariant;
        struct pair { size_t cell; size_t color; };
        Vector<pair> new_cells(coloring.size());
        for(size_t cell_idx = 0, color = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx], color++) {
            if(coloring[cell_idx] == stabilized.back() || (cell_idx > 0 && coloring[cell_idx - 1] == stabilized.back())) {
                new_cells.push({.cell = cell_idx, .color = color });
            }
            else if(coloring.m_cell_level[cell_idx] == stabilized.m_size ||
               (coloring.m_cell_end[cell_idx] < coloring.size() && coloring.m_cell_level[coloring.m_cell_end[cell_idx]] == stabilized.m_size))
                new_cells.push({.cell = cell_idx, .color = color });
        }

        for(size_t idx = 0; idx < new_cells.m_size; idx++) {
            hash::sequential32u(invariant, new_cells[idx].color);
            hash::sequential32u(invariant, coloring.cellSize(new_cells[idx].cell));
            for(size_t jdx = 0; jdx < new_cells.m_size; jdx++) {
                T adj_count = 0;
                for(size_t kdx = new_cells[idx].cell; kdx < coloring.m_cell_end[new_cells[idx].cell]; kdx++)
                    adj_count += (uint8_t) graph.adjacent(coloring[new_cells[jdx].cell], coloring[kdx]);
                hash::sequential32u(invariant, adj_count);
            }
        }

        return invariant;
    }

    HashType calculateCellSequenceInvariant() {
        HashType invariant = 0;
        if(stabilized.m_size == 0)
            return invariant;
        for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx++)
            hash::sequential32u(invariant, cell_idx);
        return invariant;
    }

    HashType calculateMultisetQuotientInvariant() {
        auto hashTriple = [](HashType x, HashType y, HashType z) {
            HashType hash = 0;
            hash::sequential32u(hash, x);
            hash::sequential32u(hash, y);
            hash::sequential32u(hash, z);
            return hash;
        };
        HashType invariant = 0;
        for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx]) {
            hash::multiset32add(invariant, cell_idx);
            for(size_t cell_jdx = 0; cell_jdx <= cell_idx; cell_jdx = coloring.m_cell_end[cell_jdx]) {
                HashType adj_count = 0;
                for(size_t idx = cell_jdx; idx < coloring.m_cell_end[cell_jdx]; idx++)
                    adj_count += graph.adjacent(coloring[cell_idx], coloring[idx]);
                hash::multiset32add(invariant, hashTriple(cell_jdx, cell_idx, adj_count));
                quotient_graph.set(cell_jdx, cell_idx, adj_count);
            }
        }
        return invariant;
    }

    HashType calculateQuotientInvariantIncrement() {
        if(stabilized.m_size == 0)
            return calculateMultisetQuotientInvariant();
        auto hashTriple = [](HashType x, HashType y, HashType z) {
            HashType hash = 0;
            hash::sequential32u(hash, x);
            hash::sequential32u(hash, y);
            hash::sequential32u(hash, z);
            return hash;
        };
        HashType invariant = invariants.back();
        BitArray is_old(coloring.size());
        BitArray is_new(coloring.size());
        Vector<size_t> old_cells(coloring.size());
        Vector<size_t> new_cells(coloring.size());
        for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx]) {
            size_t cell_end = coloring.m_cell_end[cell_idx];
            if(coloring.m_cell_level[cell_idx] < stabilized.m_size)
                is_old.set(cell_idx);
            if(coloring.m_cell_level[cell_idx] == stabilized.m_size ||
               (cell_end < coloring.size() && coloring.m_cell_level[cell_end] == stabilized.m_size))
                is_new.set(cell_idx);
            if(is_old[cell_idx] && !is_new[cell_idx])
                old_cells.push(cell_idx);
            if(is_new[cell_idx])
                new_cells.push(cell_idx);
            if(is_new[cell_idx] && !is_old[cell_idx])
                hash::multiset32add(invariant, cell_idx);
        }
        /*std::cerr << "Depth: " << stabilized.m_size << std::endl;
        std::cerr << "Old cells: ";
        for(size_t idx = 0; idx < old_cells.m_size; idx++)
            std::cerr << old_cells[idx] << ' ';
        std::cerr << std::endl;
        std::cerr << "New cells: ";
        for(size_t idx = 0; idx < new_cells.m_size; idx++)
            std::cerr << new_cells[idx] << ' ';
        std::cerr << std::endl;*/
        // Update Old <- New and New <- Old
        for(size_t old_idx = 0; old_idx < old_cells.m_size; old_idx++) {
            size_t old_cell = old_cells[old_idx];
            T prev_adj_count = 0;
            size_t prev_cell_size = 0;
            for(size_t new_idx = 0; new_idx < new_cells.m_size; new_idx++) {
                size_t new_cell = new_cells[new_idx];
                assert(new_cell != old_cell);
                if(new_cell < old_cell) {
                    if(is_old[new_cell]) {
                        prev_adj_count = quotient_graph.at(new_cell, old_cell);

                        size_t new_cell_end = coloring.m_cell_end[new_cell];
                        while(new_cell_end < coloring.size() && !is_old[new_cell_end]/*coloring.m_cell_level[new_cell_end] == stabilized.m_size*/)
                            new_cell_end = coloring.m_cell_end[new_cell_end];
                        prev_cell_size = new_cell_end - new_cell;
                        assert(prev_cell_size > 0);

#ifdef DEBUG_SLOW_ASSERTS
                        assertCellAdjCount(prev_adj_count, new_cell, new_cell_end, old_cell, coloring, graph);
#endif

                        hash::multiset32sub(invariant, hashTriple(new_cell, old_cell, prev_adj_count));
                    }
                    size_t new_cell_size = coloring.cellSize(new_cell);
                    T adj_count = (T) (prev_adj_count * new_cell_size / prev_cell_size);

#ifdef DEBUG_SLOW_ASSERTS
                    assertCellAdjCount(adj_count, new_cell, coloring.m_cell_end[new_cell], old_cell, coloring, graph);
#endif
                    quotient_graph.set(new_cell, old_cell, adj_count);
                    hash::multiset32add(invariant, hashTriple(new_cell, old_cell, adj_count));
                }
                else {
                    if(is_old[new_cell]) {
                        prev_adj_count = quotient_graph.at(old_cell, new_cell);
                    }
                    else {
#ifdef DEBUG_SLOW_ASSERTS
                        assertCellAdjCount(prev_adj_count, old_cell, coloring.m_cell_end[old_cell], new_cell, coloring, graph);
#endif
                        hash::multiset32add(invariant, hashTriple(old_cell, new_cell, prev_adj_count));
                        quotient_graph.set(old_cell, new_cell, prev_adj_count);
                    }
                }
            }
        }
        // Update New <- New
        for(size_t idx = 0; idx < new_cells.m_size; idx++) {
            size_t cell_idx = new_cells[idx];
            for(size_t jdx = 0; jdx <= idx; jdx++) {
                size_t cell_jdx = new_cells[jdx];
                if(is_old[cell_idx] && is_old[cell_jdx])
                    hash::multiset32sub(invariant, hashTriple(cell_jdx, cell_idx, quotient_graph.at(cell_jdx, cell_idx)));
                T adj_count = 0;
                for(size_t kdx = cell_jdx; kdx < coloring.m_cell_end[cell_jdx]; kdx++)
                    adj_count += graph.adjacent(coloring[kdx], coloring[cell_idx]);
#ifdef DEBUG_SLOW_ASSERTS
                assertCellAdjCount(adj_count, cell_jdx, coloring.m_cell_end[cell_jdx], cell_idx, coloring, graph);
#endif
                hash::multiset32add(invariant, hashTriple(cell_jdx, cell_idx, adj_count));
                quotient_graph.set(cell_jdx, cell_idx, adj_count);
            }
        }
#ifdef DEBUG_SLOW_ASSERTS
        assert(invariant == calculateMultisetQuotientInvariant());
#endif
        return invariant;
    }

    void calculateQuotientInvariantDecrement() {
        if(stabilized.m_size == 0)
            return;
        BitArray is_old(coloring.size());
        BitArray is_new(coloring.size());
        Vector<size_t> old_cells(coloring.size());
        Vector<size_t> new_cells(coloring.size());
        for(size_t cell_idx = 0; cell_idx < coloring.size(); cell_idx = coloring.m_cell_end[cell_idx]) {
            size_t cell_end = coloring.m_cell_end[cell_idx];
            if(coloring.m_cell_level[cell_idx] < stabilized.m_size)
                is_old.set(cell_idx);
            if(coloring.m_cell_level[cell_idx] == stabilized.m_size ||
               (cell_end < coloring.size() && coloring.m_cell_level[cell_end] == stabilized.m_size))
                is_new.set(cell_idx);
            if(is_old[cell_idx] && !is_new[cell_idx])
                old_cells.push(cell_idx);
            if(is_new[cell_idx])
                new_cells.push(cell_idx);
        }
        // Update Old <- New and New <- Old
        for(size_t old_idx = 0; old_idx < old_cells.m_size; old_idx++) {
            size_t old_cell = old_cells[old_idx];
            size_t prev_cell_size = 0;
            for(size_t new_idx = 0; new_idx < new_cells.m_size; new_idx++) {
                size_t new_cell = new_cells[new_idx];
                assert(new_cell != old_cell);
                if(new_cell < old_cell) {
                    size_t adj_count = quotient_graph.at(new_cell, old_cell);
                    if(is_old[new_cell]) {
                        size_t new_cell_size = coloring.cellSize(new_cell);
                        size_t new_cell_end = coloring.m_cell_end[new_cell];
                        while(new_cell_end < coloring.size() && !is_old[new_cell_end])
                            new_cell_end = coloring.m_cell_end[new_cell_end];
                        prev_cell_size = new_cell_end - new_cell;
                        assert(prev_cell_size > 0);
                        adj_count = adj_count * prev_cell_size / new_cell_size;

                        quotient_graph.set(new_cell, old_cell, adj_count);
                    }
                }
            }
        }
        // Update New <- New
        for(size_t idx = 0; idx < new_cells.m_size; idx++) {
            size_t cell_idx = new_cells[idx];
            for(size_t jdx = 0; jdx <= idx; jdx++) {
                size_t cell_jdx = new_cells[jdx];
                if(is_old[cell_idx] && is_old[cell_jdx]) {
                    size_t end_jdx = coloring.m_cell_end[cell_jdx];
                    while(end_jdx < coloring.size() && !is_old[end_jdx])
                        end_jdx = coloring.m_cell_end[end_jdx];
                    T adj_count = 0;
                    for(size_t kdx = cell_jdx; kdx < end_jdx; kdx++)
                        adj_count += graph.adjacent(coloring[kdx], coloring[cell_idx]);
                    quotient_graph.set(cell_jdx, cell_idx, adj_count);
                }
            }
        }
    }

    void unrefine() {
        calculateQuotientInvariantDecrement();

        size_t cell_beg = 0, cell_end = coloring.m_cell_end[0];
        size_t level = stabilized.m_size;
        while(cell_end != coloring.size()) {
            if(coloring.m_cell_level[cell_end] >= level && (level == 0 || coloring[cell_beg] != stabilized.back())) {
                cell_end = coloring.m_cell_end[cell_end];
                coloring.m_cell_end[cell_beg] = cell_end;
            }
            else {
                cell_beg = cell_end;
                cell_end = coloring.m_cell_end[cell_beg];
            }
        }
        if(invariants.m_size > 0)
            invariants.pop();
    }

    Array<T> targetCell(size_t& cell_idx) {
        cell_idx = 0;
        while(cell_idx < coloring.size() && coloring.m_cell_end[cell_idx] - cell_idx == 1)
            cell_idx++;

        if(cell_idx == coloring.size())
            return Array<T>(0);

        auto beg_ptr = coloring.m_permutation.m_forward.m_data + (size_t) cell_idx;
        auto end_ptr = coloring.m_permutation.m_forward.m_data + (size_t) coloring.m_cell_end[cell_idx];
        Array<T> cell_content(end_ptr - beg_ptr);
        std::copy(beg_ptr, end_ptr, cell_content.m_data);
        std::sort(cell_content.m_data, cell_content.m_end);

        return cell_content;
    }

    // Algorithm input
    Graph<T> graph;
    Coloring<T> input_coloring;
    Coloring<T> coloring;

    // Algorithm state
    Vector<HashType> invariants;
    Vector<T> stabilized;

    NodePath max_node;
    NodePath fst_node;

    Group<T> automorphisms;
    SymmetricMatrix<T> quotient_graph;

    // Proof
    Proof<T> proof;

    // Statistics
    struct Statistics {
        size_t tree_size = 0;
        size_t bad_nodes = 0;
        size_t orbit_prunes = 0;
        size_t max_nodes = 0;
        size_t aut_nodes = 0;
        size_t proof_size = 0;
    } statistics;
};

} // namespace

#endif // ALGORITHM_DFS_H
