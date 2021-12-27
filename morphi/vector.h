#ifndef VECTOR_H
#define VECTOR_H

#include "array.h"
#include "bitarray.h"

namespace morphi {

template<typename T>
class Vector {
public:
    Vector(size_t size) : m_array(size), m_size(0) {}

    void push(const T& val) {
        assert(m_size < m_array.m_size);
        m_array[m_size++] = val;
    }

    void pop() {
        assert(m_size > 0);
        m_size--;
    }

    void pop(size_t size) {
        assert(size <= m_size);
        m_size = size;
    }

    void copy(const Vector<T>& oth) {
        assert(oth.m_array.m_size == m_array.m_size);
        m_size = oth.m_size;
        std::copy(oth.m_array.m_data, oth.m_array.m_data + oth.m_size, m_array.m_data);
    }

    const T& back() const {
        assert(m_size > 0);
        return m_array[m_size - 1];
    }

    const T& operator[](size_t idx) const {
        assert(idx < m_size);
        return m_array[idx];
    }

    T& operator[](size_t idx) {
        assert(idx < m_size);
        return m_array[idx];
    }

    Array<T> m_array;
    size_t m_size = 0;
};

} // namespace

#endif // VECTOR_H
