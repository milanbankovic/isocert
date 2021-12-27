#ifndef PERMUTATION_H
#define PERMUTATION_H

#include "array.h"

namespace morphi {

template<typename T>
class Permutation {
public:

    Permutation() {}
    Permutation(size_t size) : m_forward(size), m_inverse(size) { }

    size_t size() const {
        return m_forward.m_size;
    }

    void swap(T a, T b) {
        assert(m_inverse[m_forward[a]] == a);
        assert(m_inverse[m_forward[b]] == b);
        if(a != b) {
            std::swap(m_forward[a], m_forward[b]);
            std::swap(m_inverse[m_forward[a]], m_inverse[m_forward[b]]);
            assert(m_inverse[m_forward[a]] == a);
            assert(m_inverse[m_forward[b]] == b);
        }
    }

    void set(T idx, T val) {
        m_forward[idx] = val;
        m_inverse[val] = idx;
        assert(m_inverse[m_forward[idx]] == idx);
    }

    void rotate(T start, T new_start, T end) {
        assert(start < end);
        std::rotate(m_forward.m_data + start, m_forward.m_data + new_start, m_forward.m_data + end);
        for(T idx = start; idx < end; idx++)
            m_inverse[m_forward[idx]] = idx;
    }

    const T& operator[](T idx) const {
        return m_forward[idx];
    }

    template<typename V>
    void copyFwd(const Permutation<V>& oth) {
        std::copy(oth.m_forward.m_data, oth.m_forward.m_end, m_forward.m_data);
        std::copy(oth.m_inverse.m_data, oth.m_inverse.m_end, m_inverse.m_data);
    }

    template<typename V>
    void copyInv(const Permutation<V>& oth) {
        std::copy(oth.m_forward.m_data, oth.m_forward.m_end, m_inverse.m_data);
        std::copy(oth.m_inverse.m_data, oth.m_inverse.m_end, m_forward.m_data);
    }

    Array<T> m_forward;
    Array<T> m_inverse;
};

} // namespace

#endif // PERMUTATION_H
