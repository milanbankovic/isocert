#ifndef _COMMON_H
#define _COMMON_H

#include <cassert>
#include <iostream>
#include <fstream>
#include <vector>
#include <iomanip>
#include <random>
#include <algorithm>
#include <map>
#include <unordered_set>
#include <memory>

using permutation = std::vector<unsigned>;

class graph {
private:
  std::vector<std::vector<bool>> _edges;
public:
  graph(unsigned n = 0)
    :_edges(n, std::vector<bool>(n, false))
  {}

  void reset(unsigned n = 0)
  {
    _edges.assign(n, std::vector<bool>(n, false));
  }
  
  void add_edge(unsigned i, unsigned j)
  {    
    _edges[i][j] = true;
    _edges[j][i] = true;
  }

  void remove_edge(unsigned i, unsigned j)
  {
    _edges[i][j] = false;
    _edges[j][i] = false;
  }

  bool edge_exists(unsigned i, unsigned j) const
  {
    return _edges[i][j];
  }

  unsigned num_nodes() const
  {
    return _edges.size();
  }

  graph apply_permutation(const permutation & perm) const
  {
    unsigned n = num_nodes();
    graph ret(n);
    for(unsigned i = 0; i < n; i++)
      for(unsigned j = 0; j <= i; j++)
	{
	  ret._edges[perm[i]][perm[j]] = _edges[i][j];
	  ret._edges[perm[j]][perm[i]] = _edges[i][j];
	}
    return ret;
  }

  bool is_automorphism(const permutation & perm) const
  {
    unsigned n = num_nodes();
    for(unsigned i = 0; i < n; i++)
      for(unsigned j = 0; j <= i; j++)
	if(_edges[perm[i]][perm[j]] != _edges[i][j])
	  return false;
    return true;	
  }
  
  int compare_to(const graph & g) const
  {
    unsigned n = num_nodes();
    for(unsigned i = 0; i < n; i++)
      for(unsigned j = 0; j <= i; j++)
	{
	  if(_edges[i][j] > g._edges[i][j])
	    return 1;
	  else if(_edges[i][j] < g._edges[i][j])
	    return -1;
	}
    return 0;	
  }
  
  void out(std::ostream & ostr) const
  {
    ostr << "   ";
    for(unsigned i = 0; i < num_nodes(); i++)
      ostr << std::setw(2) << i  << " ";
    ostr << std::endl;
    for(unsigned i = 0; i < num_nodes(); i++)
      {
	ostr << std::setw(2) << i << " ";
	
	for(unsigned j = 0; j < num_nodes(); j++)
	  {
	    ostr << std::setw(2) << _edges[i][j] << " ";	    
	  }
	ostr << std::endl;
      }
  }

  void in(std::istream & istr)
  {
    std::string s, t;
    unsigned n, m;
    istr >> s >> t >> n >> m;
    if(!istr || s != "p" || t != "edge")
      {
	std::cerr << "error reading file" << std::endl;
	exit(1);
      }
    reset(n);
    for(unsigned k = 0; k < m; k++)
      {
	unsigned i,j;
	istr >> s >> i >> j;
	if(s != "e")
	  {
	    std::cerr << "error reading file" << std::endl;
	    exit(1);
	  }
	add_edge(i-1,j-1);
      }
  }
};

inline
std::ostream & operator << (std::ostream & ostr, const graph & g)
{
  g.out(ostr);
  return ostr;
}

inline
std::istream & operator >> (std::istream & istr, graph & g)
{
  g.in(istr);
  return istr;
}

template <typename T>
std::enable_if_t<std::is_integral_v<T> && sizeof(T) == 4 && std::is_unsigned_v<T>, T>
hash32(T value)
{
  value++;
  value ^= value >> 17;
  value *= 0xed5ad4bb;
  value ^= value >> 11;
  value *= 0xac4c1b51;
  value ^= value >> 15;
  value *= 0x31848bab;
  value ^= value >> 14;
  return value;
}

class coloring {
private:
  std::vector<unsigned> _node_colors;
  std::vector<std::vector<unsigned>> _cells;
  unsigned _invariant = 0;

  static unsigned hash_triple(unsigned x, unsigned y, unsigned z)
  {
    return hash32(hash32(hash32(x) ^ y) ^ z);
  }
  
  static unsigned add_invariant(unsigned invariant, unsigned x)
  {
    return invariant + hash32(x) + 1;
  }
  
  void calculate_invariant(const graph & g)
  {
    static std::vector<unsigned> cell_start;
    cell_start.clear();
    cell_start.push_back(0);
    _invariant = 0;
    for(unsigned i = 0; i < _cells.size(); i++)
      {
	_invariant = add_invariant(_invariant, cell_start.back());
	cell_start.push_back(cell_start.back() + _cells[i].size());
      }


    for(unsigned i = 0; i < _cells.size(); i++)
      {
	for(unsigned j = i; j < _cells.size(); j++)
	  {
	    unsigned v = _cells[j][0];
	    unsigned count = 0;
	    
	    for(unsigned l = 0; l < _cells[i].size(); l++)
	      {
		if(g.edge_exists(v, _cells[i][l]))
		  count++;
	      }
	    
	    _invariant = add_invariant(_invariant, hash_triple(cell_start[i], cell_start[j], count));
	  }
      }    
  }
    
public:
  coloring(unsigned n = 0)
    :_node_colors(n, 0),
     _cells(1, std::vector<unsigned>(n))
  {
    for(unsigned i = 0; i < n; i++)
      _cells[0][i] = i;
  }

  coloring(std::vector<unsigned> && node_colors, const graph & g, bool calculate = false)
    :_node_colors(std::move(node_colors))
  {
    unsigned num_of_colors = 0;
    for(unsigned i = 0; i < _node_colors.size(); i++)
      if(_node_colors[i] + 1 > num_of_colors)
	num_of_colors = _node_colors[i] + 1;
    _cells.resize(num_of_colors);
    
    for(unsigned i = 0; i < _node_colors.size(); i++)
      {
	_cells[_node_colors[i]].push_back(i);
      }

    if(calculate)
      calculate_invariant(g);
  }

  
  coloring(std::vector<std::vector<unsigned>> && cells, unsigned num_of_nodes, const graph & g, bool calculate = true)
    :_node_colors(num_of_nodes),
     _cells(std::move(cells)),
     _invariant(0)
  {
    for(unsigned i = 0; i < _cells.size(); i++)
      for(unsigned j = 0; j < _cells[i].size(); j++)
	_node_colors[_cells[i][j]] = i;

    if(calculate)
      calculate_invariant(g);    
  }
  
  unsigned node_color(unsigned i) const
  {
    return _node_colors[i];
  }

  const std::vector<unsigned> node_colors() const
  {
    return _node_colors;
  }
  
  const std::vector<std::vector<unsigned>> & cells() const
  {
    return _cells;
  }
  
  const std::vector<unsigned> & cell(unsigned j) const
  {
    return _cells[j];
  }

  unsigned num_nodes() const
  {
    return _node_colors.size();
  }
  
  bool is_discrete() const
  {
    for(unsigned i = 0; i < _cells.size(); i++)
      if(_cells[i].size() > 1)
	return false;
    return true;
  }

  unsigned num_cells() const
  {
    return _cells.size();
  }

  const unsigned & invariant() const
  {
    return _invariant;
  }
  
  coloring apply_permutation(const permutation & perm) const
  {
    std::vector<unsigned> colors(num_nodes());
    for(unsigned i = 0; i < colors.size(); i++)
      colors[perm[i]] = _node_colors[i];
    
    return coloring(std::move(colors), _cells.size(), _invariant);
  }

  bool is_automorphism(const permutation & perm) const
  {
    for(unsigned i = 0; i < _node_colors.size(); i++)
      if(_node_colors[perm[i]] != _node_colors[i])
	return false;
    return true;
  }
  
  permutation get_permutation() const
  {
    assert(is_discrete());
    return _node_colors;
  }
  
  void out(std::ostream & ostr) const
  {
    for(unsigned j = 0; j < _cells.size(); j++)
      {
	ostr << "{ ";
	for(unsigned i = 0; i < _cells[j].size(); i++)
	  ostr << _cells[j][i] <<  " ";
	ostr << " } ";
      }
  }

  bool operator == (const coloring & c) const
  {
    return _node_colors == c._node_colors;
  }

  bool operator != (const coloring & c) const
  {
    return !(*this == c);
  }
};

inline
std::ostream & operator << (std::ostream & ostr, const coloring & c)
{
  c.out(ostr);
  return ostr;
}

template <typename T>
unsigned read_utf8(T & istr)
{

  char c; 
  if(istr.read(&c, 1))
    {
      unsigned code = 0;
      if((c & 0x80) == 0)
	{
	  code = c & 0x7F;
	}

      else if((c & 0x20) == 0)
	{
	  code |= (c & 0x1F) << 6;
	  istr.read(&c, 1);
	  code |= (c & 0x3F);
	}
      else if((c & 0x10) == 0)
	{
	  code |= (c & 0xF) << 12;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 6;
	  istr.read(&c, 1);
	  code |= (c & 0x3F);
	}
      else if((c & 0x08) == 0)
	{
	  code |= (c & 0x7) << 18;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 12;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 6;
	  istr.read(&c, 1);
	  code |= (c & 0x3F);
	}
      else if((c & 0x04) == 0)
	{
	  code |= (c & 0x3) << 24;
	  istr.read(&c, 1);	  
	  code |= (c & 0x3F) << 18;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 12;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 6;
	  istr.read(&c, 1);
	  code |= (c & 0x3F);
	}
      else
	{
	  code |= (c & 0x1) << 30;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 24;
	  istr.read(&c, 1);	  
	  code |= (c & 0x3F) << 18;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 12;
	  istr.read(&c, 1);
	  code |= (c & 0x3F) << 6;
	  istr.read(&c, 1);
	  code |= (c & 0x3F);
	}
      return code;
    }  
  return (unsigned)(-1);
}

enum class rule_type : unsigned {
  COLORING_AXIOM = 0,
  INDIVIDUALIZE,
  SPLIT_COLORING,
  EQUITABLE,
  TARGET_CELL,
  INVARIANT_AXIOM,
  INVARIANTS_EQUAL,
  INVARIANTS_EQUAL_SYM,
  ORBITS_AXIOM,
  MERGE_ORBITS,
  PRUNE_INVARIANT,
  PRUNE_LEAF,
  PRUNE_AUTOMORPHISM,
  PRUNE_PARENT,
  PRUNE_ORBITS,
  PATH_AXIOM,
  EXTEND_PATH,
  CANONICAL_LEAF
};

#endif // _COMMON_H
