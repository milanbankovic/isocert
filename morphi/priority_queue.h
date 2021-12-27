#ifndef PRIORITY_QUEUE_H
#define PRIORITY_QUEUE_H

#include "array.h"
#include "bitarray.h"

namespace morphi {

template<typename T>
class PriorityQueue {
public:
    PriorityQueue(size_t capacity) : m_heap(capacity), m_elem(capacity) {}

    void push(T val) {
        assert(m_size < m_heap.m_size);
        m_elem.set(val);
        m_heap[m_size++] = val;
        pushUp();
    }

    T pop() {
        assert(m_size > 0);
        m_elem.clear(m_heap[0]);
        std::swap(m_heap.m_data[0], m_heap.m_data[--m_size]);
        pushDown();
        return m_heap[m_size];
    }

    bool contains(T val) const {
        return m_elem[val];
    }

    void pushUp() {
        assert(m_size > 0);
        size_t idx = m_size - 1;
        while(idx > 0) {
            size_t parent = (idx - 1) >> 1;
            if(m_heap[idx] > m_heap[parent])
                break;
            std::swap(m_heap.m_data[idx], m_heap.m_data[parent]);
            idx = parent;
        }
    }

    void pushDown() {
        size_t idx = 0;
        while(idx < m_size) {
            size_t min_idx = idx;
            size_t child1 = (idx << 1) + 1;
            size_t child2 = child1 + 1;
            if(child1 < m_size && m_heap[min_idx] > m_heap[child1])
                min_idx = child1;
            if(child2 < m_size && m_heap[min_idx] > m_heap[child2])
                min_idx = child2;
            if(min_idx == idx)
                break;
            std::swap(m_heap.m_data[idx], m_heap.m_data[min_idx]);
            idx = min_idx;
        }
    }

    Array<T> m_heap;
    BitArray m_elem;
    size_t m_size = 0;
};

} // namespace

#endif // PRIORITY_QUEUE_H
