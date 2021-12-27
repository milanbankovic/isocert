#ifndef COLORING_H
#define COLORING_H

#include "permutation.h"
#include "hash.h"
#include "vector.h"

namespace morphi {

template<typename T>
class Coloring {
public:

    // colors: [vertex, color, vertex, color, ...]
    Coloring(size_t size, uint32_t* colors) : m_permutation(size), m_cell_end(size, 0), m_cell_level(size, 0) {
        std::sort((uint64_t*) colors, (uint64_t*) colors + size); // BYTE ORDER?
        size_t cell_prev = 0;
        m_cell_end[0] = size;
        for(size_t idx = 0; idx < size; idx++) {
            m_permutation.m_forward[idx] = colors[2 * idx];
            m_permutation.m_inverse[colors[2 * idx]] = idx;
            if(idx > 0 && colors[2 * idx + 1] != colors[2 * idx - 1]) {
                m_cell_end[cell_prev] = idx;
                m_cell_end[idx] = size;
                cell_prev = idx;
            }
        }
    }

    Coloring(size_t size) : m_permutation(size), m_cell_end(size), m_cell_level(size) {}

    size_t size() const {
        return m_permutation.size();
    }

    const T& operator[](size_t idx) const {
        return m_permutation[idx];
    }

    void copy(const Coloring<T>& oth) {
        m_permutation.copyFwd(oth.m_permutation);
        std::copy(oth.m_cell_end.m_data, oth.m_cell_end.m_end, m_cell_end.m_data);
        std::copy(oth.m_cell_level.m_data, oth.m_cell_level.m_end, m_cell_level.m_data);
    }

    T indexOf(T vertex) const {
        return m_permutation.m_inverse[vertex];
    }

    size_t cellSize(size_t cell_idx) const {
        return m_cell_end[cell_idx] - cell_idx;
    }

    void rotate(size_t cell_beg, size_t cell_end, size_t level) {
        // proveriti
        if(m_cell_end[cell_beg] == cell_end)
            return;
        m_permutation.rotate(cell_beg, m_cell_end[cell_beg], cell_end);
        Vector<size_t> cell_sizes(cell_end - cell_beg);
        for(size_t cell = m_cell_end[cell_beg]; cell != cell_end; cell = m_cell_end[cell])
            cell_sizes.push(cellSize(cell));
        for(size_t idx = 0; idx < cell_sizes.m_size; idx++) {
            m_cell_end[cell_beg] = cell_beg + cell_sizes[idx];
            cell_beg = m_cell_end[cell_beg];
            m_cell_level[cell_beg] = level;
        }
        m_cell_end[cell_beg] = cell_end;
    }

    Permutation<T> m_permutation;
    Array<T> m_cell_end;
    Array<T> m_cell_level;
};

template<typename T>
std::ostream& operator<<(std::ostream& output, const Coloring<T>& c) {
    for(size_t cell = 0; cell < c.size(); cell = c.m_cell_end[cell]) {
        if(cell > 0)
            output << ']';
        output << /*(size_t)c.m_cell_level[cell] <<*/ "[ ";
        for(size_t idx = cell; idx < c.m_cell_end[cell]; idx++)
            output << (size_t) c.m_permutation[idx] << ' ';
    }
    output << ']';
    return output;
}

} // namespace

#endif // COLORING_H
