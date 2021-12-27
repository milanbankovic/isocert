#ifndef ALGORITHM_SELECTOR_H
#define ALGORITHM_SELECTOR_H

#include <cstdint>
#include <limits>
#include <string>
#include <iostream>
#include <algorithm>
#include <numeric>

#include "array.h"
#include "vector.h"
#include "permutation.h"
#include "utility.h"
#include "algorithm_argo.h"

namespace morphi {

class AlgorithmSelector {
public:

    struct Params;

    // AlgorithmSelector(command line options, input stream, other stuff)
    AlgorithmSelector(std::istream& input, const Options& opt) : m_options(opt) {
        fromStream(input);
        m_canon = Permutation<uint32_t>(m_vertices);

        m_params.relabeling = Permutation<uint32_t>(m_vertices);
        if(opt.relabel)
            relabel();
    }

    void relabel() {
        m_options.relabel = true;

        // Generate random relabeling permutation
        std::iota(m_params.relabeling.m_forward.m_data, m_params.relabeling.m_forward.m_end, 0);
        std::random_shuffle(m_params.relabeling.m_forward.m_data, m_params.relabeling.m_forward.m_end);

        // Calculate inverse permutation
        for(size_t idx = 0; idx < m_vertices; idx++)
            m_params.relabeling.m_inverse[m_params.relabeling.m_forward[idx]] = idx;

        // Relabel coloring input
        for(size_t idx = 0; idx < m_vertices; idx++)
            m_colors[2 * idx] = m_params.relabeling[m_colors[2 * idx]];

        // Relabel graph input
        for(size_t idx = 0; idx < 2 * m_edges; idx++)
            m_edge_list[idx] = m_params.relabeling[m_edge_list[idx]];
    }

    void fromStream(std::istream& input) {
        std::string s;
        input >> s;
        while(s == "c") {
            input.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
            input >> s;
        }

        // trebalo bi da je s == "p"
        // procitaj i skipuj "edge"
        input >> s;

        size_t vertices, edges;
        input >> vertices >> edges;

        Array<uint32_t> colors(2 * vertices, 0);
        Vector<uint32_t> edge_list(2 * edges);

        for(size_t idx = 0; idx < vertices; idx++)
            colors.m_data[2 * idx] = idx;

        uint32_t a, b;
        while(input >> s) {
            input >> a >> b;
            if(s == "n")
                colors[2 * a - 1] = b;
            else if(s == "e") {
                edge_list.push(a - 1);
                edge_list.push(b - 1);
            }
        }

        m_vertices = vertices;
        m_edges = edges;
        m_colors = std::move(colors);
        m_edge_list = std::move(edge_list.m_array);
    }

    template<typename AlgorithmType>
    void runWith() {
        AlgorithmType solver(m_vertices, m_edges, m_edge_list, m_colors, m_options.aut_limit, m_options.proof_type, m_options.proof_file);

        m_canon.copyFwd(solver.solve());

        if(m_options.proof_type == ProofType::PrunedTree) {
            solver.generateProof();
        }
        else if(m_options.proof_type == ProofType::None){
            if(m_options.relabel) {
                for(size_t idx = 0; idx < m_vertices; idx++)
                    m_canon.set(idx, m_params.relabeling[m_canon[idx]]);
            }

            if(m_options.relabel) {
                for(size_t i = 0; i < m_vertices; i++)
                    for(size_t j = 0; j < m_vertices; j++)
                        std::cout << solver.graph.adjacent(m_canon.m_inverse[m_params.relabeling[i]], m_canon.m_inverse[m_params.relabeling[j]]);
                std::cout << std::endl;
            }
            else {
                for(size_t i = 0; i < m_vertices; i++)
                    for(size_t j = 0; j < m_vertices; j++)
                        std::cout << solver.graph.adjacent(m_canon.m_inverse[i], m_canon.m_inverse[j]);
                std::cout << std::endl;
            }
        }
    }

    void run() {
        // gomilu if-else zavisno od opcija i velicine grafa?
        if(m_vertices <= 0xff)
            runWith< AlgorithmArgonaut<uint8_t, uint32_t> >();
        else if(m_vertices <= 0xffff)
            runWith< AlgorithmArgonaut<uint16_t, uint32_t> >();
        else
            runWith< AlgorithmArgonaut<uint32_t, uint32_t> >();
    }

    // Command line options
    Options m_options;

    struct Params {
        Permutation<uint32_t> relabeling;
    } m_params;

    // Raw graph input
    size_t m_vertices;
    size_t m_edges;
    Array<uint32_t> m_colors;
    Array<uint32_t> m_edge_list;

    // Algorithm output
    Permutation<uint32_t> m_canon;
};

} // namespace

#endif // ALGORITHM_SELECTOR_H
