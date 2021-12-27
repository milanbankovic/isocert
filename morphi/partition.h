#ifndef PARTITION_H
#define PARTITION_H

#include <algorithm>

#include "array.h"
#include "vector.h"

namespace morphi {

template<typename T>
class Partition {
public:

    struct PartitionClass {
        T point;
        T size;
        T parent;
    };

    Partition(size_t size) : m_partition(size) {
        for(size_t idx = 0; idx < size; idx++)
            m_partition[idx] = {.point = (T) idx, .size = 1, .parent = (T) idx};
    }

    T mcr(T elem) {
        return m_partition[representative(elem)].point;
    }

    T representative(T elem) {
        assert(elem < m_partition.m_size);
        Vector<T> path(m_partition.m_size);
        while(elem != m_partition[elem].parent) {
            path.push(elem);
            elem = m_partition[elem].parent;
        }

        // Union-Find path compression
        for(size_t idx = 0; idx < path.m_size; idx++)
            m_partition[path[idx]].parent = elem;

        return elem;
    }

    void merge(T a, T b) {
        T pa = representative(a);
        T pb = representative(b);
        if(pa == pb)
            return;
        if(m_partition[pa].size < m_partition[pb].size) {
            m_partition[pa].parent = pb;
            m_partition[pb].size += m_partition[pa].size;
            m_partition[pb].point = std::min(m_partition[pa].point, m_partition[pb].point);
        }
        else {
            m_partition[pb].parent = pa;
            m_partition[pa].size += m_partition[pb].size;
            m_partition[pa].point = std::min(m_partition[pa].point, m_partition[pb].point);
        }
    }

    Vector<T> classOf(T elem) {
        T p = mcr(elem);
        Vector<T> class_content(m_partition.m_size);
        for(size_t idx = 0; idx < m_partition.m_size; idx++)
            if(mcr(idx) == p)
                class_content.push(idx);
        return class_content;
    }

    Array<PartitionClass> m_partition;
};

} // namespace

#endif // PARTITION_H
