#ifndef BITARRAY_H
#define BITARRAY_H

#include "array.h"

namespace morphi {

class BitArray {
public:

    BitArray(size_t size) : m_data((size + 7) >> 3, 0) {}

    void set(size_t idx) {
        size_t byte_idx = idx >> 3;
        size_t bit_idx  = idx & 0x7;
        m_data[byte_idx] |= (1 << bit_idx);
    }

    void clear(size_t idx) {
        size_t byte_idx = idx >> 3;
        size_t bit_idx  = idx & 0x7;
        m_data[byte_idx] &= ~(1 << bit_idx);
    }

    bool operator[](size_t idx) const {
        size_t byte_idx = idx >> 3;
        size_t bit_idx  = idx & 0x7;
        return m_data[byte_idx] & (1 << bit_idx);
    }

    Array<uint8_t> m_data;
};

} // namespace

#endif // BITARRAY_H
