#ifndef MATRIX_H
#define MATRIX_H

#include "array.h"

namespace morphi {

template<typename T>
class Matrix {
public:
    Matrix(size_t rows, size_t cols) : m_rows(rows), m_cols(cols), m_data(rows * cols) { }

    const T& at(size_t r, size_t c) const {
        return m_data[r * m_cols + c];
    }

    const T& set(size_t r, size_t c, const T& val) {
        return m_data[r * m_cols + c] = val;
    }

    Array<T> m_data;
    size_t m_rows = 0;
    size_t m_cols = 0;
};

template<typename T>
class SymmetricMatrix {
public:
    SymmetricMatrix(size_t rows) : m_rows(rows), m_data(rows * (rows + 1) / 2) {}

    const T& at(size_t r, size_t c) const {
        return m_data[matrixAt(r, c)];
    }

    void set(size_t r, size_t c, const T& val) {
        m_data[matrixAt(r, c)] = val;
    }

    size_t matrixAt(size_t r, size_t c) const {
        assert(r <= c);
        return r * (2 * m_rows - r - 1) / 2 + c;
    }

    size_t m_rows = 0;
    Array<T> m_data;
};

} // namespace

#endif // MATRIX_H
