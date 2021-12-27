#ifndef ARRAY_H
#define ARRAY_H

#include "memory.h"
#include <algorithm>
#include <iostream>

namespace morphi {

template<typename T>
class Array {
public:
    Array() {}
    Array(size_t size) : m_size(size) {
        m_data = global_alloc.alloc<T>(size);
        m_end = m_data + m_size;
    }

    ~Array() {
        if(m_size)
            global_alloc.dealloc<T>(m_size);
    }

    Array(const Array&) = delete;
    Array& operator=(const Array&) = delete;

    Array(Array&& oth) :
        m_data(std::exchange(oth.m_data, nullptr)),
        m_end(std::exchange(oth.m_end, nullptr)),
        m_size(std::exchange(oth.m_size, 0)) {}
    Array& operator=(Array&& oth) {
        assert(m_size == 0);
        std::swap(m_data, oth.m_data);
        std::swap(m_end, oth.m_end);
        std::swap(m_size, oth.m_size);
        return *this;
    }

    Array(size_t size, const T& default_val) : Array(size) {
        std::fill(m_data, m_end, default_val);
    }

    const T& operator[](size_t idx) const {
        return m_data[idx];
    }

    T& operator[](size_t idx) {
        return m_data[idx];
    }


    T* m_data = nullptr;
    T* m_end = nullptr;
    size_t m_size = 0;
};

} // namespace

#endif // ARRAY_H
