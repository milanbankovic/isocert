#ifndef PROOF_H
#define PROOF_H

#include <fstream>
#include "vector.h"
#include "coloring.h"

namespace morphi {

template<typename T>
class Proof {
public:

    Proof(std::string filename) : proof_file(filename) {}

    void open() {
        out.open(proof_file.c_str(), std::ios::out | std::ios::binary);
    }

    void close() {
        out.close();
    }

    void writeUTF8(uint32_t code) {
        //std::cerr << code << ' ';
      static char buff[6];
      unsigned count = 0;
      // one byte (up to 7 bits)
      if((code & 0xFFFFFF80) == 0)
        {
          buff[count++] = (char)code;
        }
      // two bytes (up to 11 bits)
      else if((code & 0xFFFFF800) == 0)
        {
          char c;

          c = 0xC0 | (0x1F & (code >> 6));
          buff[count++] = c;
          c = 0x80 | (0x3F & code);
          buff[count++] = c;
        }
      // three bytes (up to 16 bits)
      else if((code & 0xFFFF0000) == 0)
        {
          char c;

          c = 0xE0 | (0xF & (code >> 12));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 6));
          buff[count++] = c;
          c = 0x80 | (0x3F & code);
          buff[count++] = c;
        }
      // four bytes (up to 21 bits)
      else if((code & 0xFFE00000) == 0)
        {
          char c;

          c =  0xF0 | (0x7 & (code >> 18));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 12));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 6));
          buff[count++] = c;
          c = 0x80 | (0x3F & code);
          buff[count++] = c;
        }
      // five bytes (up to 26 bits)
      else if((code & 0xFC000000) == 0)
        {
          char c;

          c = 0xF8 | (0x3 & (code >> 24));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 18));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 12));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 6));
          buff[count++] = c;
          c = 0x80 | (0x3F & code);
          buff[count++] = c;
        }
      else // six bytes (up to 31 bits)
        {
          char c;

          c = 0xFC | (0x1 & (code >> 30));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 24));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 18));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 12));
          buff[count++] = c;
          c = 0x80 | (0x3F & (code >> 6));
          buff[count++] = c;
          c = 0x80 | (0x3F & code);
          buff[count++] = c;
        }
      out.write(buff, count);
    }



    void writeColoring(const Coloring<T>& coloring, size_t level) {
        Array<T> colors(coloring.size());
        T color = 0;
        size_t idx = 0;
        for(size_t cell_idx = 0; cell_idx != coloring.size(); cell_idx = coloring.m_cell_end[cell_idx]) {
            while(idx < coloring.m_cell_end[cell_idx])
                colors[coloring[idx++]] = color;
            if(idx < coloring.size() && coloring.m_cell_level[idx] <= level)
                color++;
        }
        //std::cerr << "c[ ";
        for(auto ptr = colors.m_data; ptr != colors.m_end; ptr++)
            writeUTF8(*ptr);
        //std::cerr << "] ";
    }

    void writeColoring(const Coloring<T>& coloring) {
        writeColoring(coloring, coloring.size());
    }

    void writeNode(const Vector<T>& node, size_t level) {
        writeUTF8(level);
        //std::cerr << "@ [ ";
        for(size_t idx = 0; idx < level; idx++)
            ////std::cerr << (size_t) node[idx] << ' ';
            writeUTF8(node[idx]);
        //std::cerr << "] ";
    }

    void writeNode(const Vector<T>& node) {
        writeNode(node, node.m_size);
    }

    void writeArray(const Array<T>& array) {
        //std::cerr << "[ ";
        for(auto ptr = array.m_data; ptr != array.m_end; ptr++)
            writeUTF8(*ptr);
        //std::cerr << "] ";
    }

    void writeArraySized(const Array<T>& array) {
        writeUTF8(array.m_size);
        writeArray(array);
    }

    void coloringAxiom() {
        writeUTF8(0);
        //std::cerr << std::endl;
    }

    void individualize(const Vector<T>& node, T vertex, const Coloring<T>& coloring) {
        writeUTF8(1);
        writeNode(node);
        writeUTF8(vertex);
        writeColoring(coloring);
        //std::cerr << std::endl;
    }

    void splitColoring(const Vector<T>& node, const Coloring<T>& coloring) {
        writeUTF8(2);
        writeNode(node);
        writeColoring(coloring);
        //std::cerr << std::endl;
    }

    void equitable(const Vector<T>& node, const Coloring<T>& coloring) {
        writeUTF8(3);
        writeNode(node);
        writeColoring(coloring);
        //std::cerr << std::endl;
    }

    void targetCell(const Vector<T>& node, const Coloring<T>& coloring) {
        writeUTF8(4);
        writeNode(node);
        writeColoring(coloring);
        //std::cerr << std::endl;
    }

    void invariantAxiom(const Vector<T>& node) {
        writeUTF8(5);
        writeNode(node);
        //std::cerr << std::endl;
    }

    void invariantsEqual(size_t level,
                         const Vector<T>& node1, const Coloring<T>& coloring1,
                         const Vector<T>& node2, const Coloring<T>& coloring2) {
        writeUTF8(6);
        writeNode(node1, level);
        writeColoring(coloring1, level);
        writeNode(node2, level);
        writeColoring(coloring2, level);
        //std::cerr << std::endl;
    }

    void invariantsEqualSym(size_t level, const Vector<T>& node1, const Vector<T>& node2) {
        writeUTF8(7);
        writeNode(node1, level);
        writeNode(node2, level);
    }

    void orbitsAxiom(T vertex, const Vector<T>& node) {
        writeUTF8(8);
        writeUTF8(vertex);
        writeNode(node);
        //std::cerr << std::endl;
    }

    void mergeOrbits(const Vector<T>& orbit1, const Vector<T>& orbit2,
                     const Vector<T>& node, const Array<T>& automorphism,
                     T vertex1, T vertex2) {
        writeUTF8(9);
        writeNode(orbit1);
        writeNode(orbit2);
        writeNode(node);
        writeArray(automorphism);
        writeUTF8(vertex1);
        writeUTF8(vertex2);
        //std::cerr << std::endl;
    }

    void pruneInvariant(size_t level,
                        const Vector<T>& node1, const Coloring<T>& coloring1,
                        const Vector<T>& node2, const Coloring<T>& coloring2) {
        writeUTF8(10);
        writeNode(node1, level);
        writeColoring(coloring1, level);
        writeNode(node2, level);
        writeColoring(coloring2, level);
        //std::cerr << std::endl;
    }

    void pruneLeaf(size_t level,
                   const Vector<T>& node1, const Coloring<T>& coloring1,
                   const Vector<T>& node2, const Coloring<T>& coloring2) {
        writeUTF8(11);
        writeNode(node1, level);
        writeColoring(coloring1, level);
        writeNode(node2, level);
        writeColoring(coloring2, level);
        //std::cerr << std::endl;
    }

    void pruneAutomorphism(size_t level, const Vector<T>& node1, const Vector<T>& node2, const Array<T>& automorphism) {
        writeUTF8(12);
        writeNode(node1, level);
        writeNode(node2, level);
        writeArray(automorphism);
        //std::cerr << std::endl;
    }

    void pruneParent(size_t level, const Vector<T>& node, const Array<T>& cell) {
        writeUTF8(13);
        writeNode(node, level);
        writeArraySized(cell);
        //std::cerr << std::endl;
    }

    void pruneOrbits(const Vector<T>& orbit, const Vector<T>& node, T vertex1, T vertex2) {
        writeUTF8(14);
        writeNode(orbit);
        writeNode(node);
        writeUTF8(vertex1);
        writeUTF8(vertex2);
        //std::cerr << std::endl;
    }

    void pathAxiom() {
        writeUTF8(15);
        //std::cerr << std::endl;
    }

    void extendPath(size_t level, const Vector<T>& node, const Array<T>& cell, T vertex) {
        writeUTF8(16);
        writeNode(node, level);
        writeArraySized(cell);
        writeUTF8(vertex);
        //std::cerr << std::endl;
    }

    void canonicalLeaf(const Vector<T>& node, const Array<T>& permutation) {
        writeUTF8(17);
        writeNode(node);
        writeArray(permutation);
        //std::cerr << std::endl;
    }

    std::string proof_file;
    std::ofstream out;
};

} // namespace

#endif // PROOF_H
