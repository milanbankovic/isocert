#ifndef MEMORY_H
#define MEMORY_H

#include <cstddef>
#include <cassert>
#include <sys/mman.h>
#include <cstdlib>

namespace morphi {

class Allocator {
public:

    bool reserve(size_t bytes) {
        if((m_start = mmap(nullptr, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)) != MAP_FAILED) {
        //if((m_start = malloc(bytes)) != nullptr) {
            m_bytes = bytes;
            return true;
        }
        return false;
    }

    template<typename T>
    T* alloc(size_t size) {
        assert(m_start != nullptr);

        size_t array_bytes = size * sizeof(T);
        align(array_bytes);
        assert(m_offset + array_bytes <= m_bytes);

        T* array_ptr = (T*)((std::byte*)m_start + m_offset);
        m_offset += array_bytes;
        return array_ptr;
    }

    template<typename T>
    void dealloc(size_t size) {
        size_t array_bytes = size * sizeof(T);
        align(array_bytes);
        assert(array_bytes <= m_offset);
        m_offset -= array_bytes;
    }

    inline static void align(size_t& size) {
        if(size & 0x7)
            size += 0x8 - (size & 0x7);
    }

private:

    void* m_start = nullptr;
    size_t m_bytes = 0;
    size_t m_offset = 0;
};

Allocator global_alloc;

} // namespace

#endif // MEMORY_H
