#ifdef QT_QML_DEBUG
#ifndef ASSERTIONS_H
#define ASSERTIONS_H

#include <algorithm>

#include "array.h"
#include "bitarray.h"
#include "coloring.h"

namespace morphi {

template<typename T>
void assertArrayElementsDistinct(const Array<T>& array) {
    Array<T> tmp(array.m_size);
    std::copy(array.m_data, array.m_end, tmp.m_data);
    std::sort(tmp.m_data, tmp.m_end);
    assert(std::adjacent_find(tmp.m_data, tmp.m_end) == tmp.m_end);
}

void assertBitMatrixIndex(size_t a, size_t b, size_t index, size_t vertices) {
    size_t i = 0;
    size_t j = 0;
    size_t len = 0;
    size_t row = vertices - 1;
    while(len + row <= index) {
        len += row;
        row--;
        i++;
    }
    j = i + 1 + index - len;
    assert(a == i);
    assert(b == j);
}

template<typename T>
void assertValidColoring(const Coloring<T>& coloring) {
    for(size_t idx = 0; idx < coloring.size(); idx = coloring.m_cell_end[idx]) {
        assert(coloring.m_cell_end[idx] > idx);
        assert(coloring.m_cell_end[idx] <= coloring.size());
    }
    assertArrayElementsDistinct(coloring.m_permutation.m_forward);
    assert(*std::min_element(coloring.m_permutation.m_forward.m_data, coloring.m_permutation.m_forward.m_end) == (T)0);
    assert(*std::max_element(coloring.m_permutation.m_forward.m_data, coloring.m_permutation.m_forward.m_end) == (T)(coloring.size() - 1));
}

template<typename T>
void assertCellSplittingValid(const Coloring<T>& coloring, size_t cell_beg, size_t cell_end, const Array<T>& adj_count, size_t level) {
    for(size_t cell_idx = cell_beg; cell_idx != cell_end; cell_idx = coloring.m_cell_end[cell_idx]) {
        if(cell_idx != cell_beg) {
            assert(adj_count[coloring[cell_idx]] != adj_count[coloring[cell_idx - 1]]);
            assert(coloring.m_cell_level[cell_idx] == level);
        }
    }
}

template<typename T, typename GraphT>
void assertColoringSplittingValid(const Coloring<T>& coloring, const GraphT& graph, size_t work_cell, size_t work_size) {
       Array<T> tmp(coloring.size(), 0);
       for(size_t idx = 0; idx < coloring.size(); idx++)
           for(size_t jdx = work_cell; jdx < work_cell + work_size; jdx++)
               tmp[idx] += graph.adjacent(coloring[idx], coloring[jdx]);
       for(size_t cell = 0; cell < coloring.size(); cell = coloring.m_cell_end[cell])
           for(size_t idx = cell + 1; idx < coloring.m_cell_end[cell]; idx++)
               assert(tmp[idx] == tmp[idx - 1]);
}

template<typename T, typename GraphT>
void assertEquitableColoring(const Coloring<T>& coloring, const GraphT& graph) {
    for(size_t cell1 = 0; cell1 < coloring.size(); cell1 = coloring.m_cell_end[cell1])
        for(size_t cell2 = 0; cell2 < coloring.size(); cell2 = coloring.m_cell_end[cell2]) {
            T cell1_adj_count = 0;
            for(size_t idx = cell1; idx < coloring.m_cell_end[cell1]; idx++) {
                T adj_count = 0;
                for(size_t jdx = cell2; jdx < coloring.m_cell_end[cell2]; jdx++)
                    adj_count += (T) graph.adjacent(coloring[idx], coloring[jdx]);
                if(idx == cell1)
                    cell1_adj_count = adj_count;
                else
                    assert(adj_count == cell1_adj_count);
            }
        }
}

template<typename T, typename GraphT>
void assertCellAdjCount(T adj_count, size_t cell_beg, size_t cell_end, size_t cell_oth, const Coloring<T>& coloring, const GraphT& graph) {
    T actual_adj_count = 0;
    for(size_t idx = cell_beg; idx < cell_end; idx++)
        actual_adj_count += graph.adjacent(coloring[idx], coloring[cell_oth]);
    assert(adj_count == actual_adj_count);
}

}
#endif // ASSERTIONS_H

#endif // DEBUG

