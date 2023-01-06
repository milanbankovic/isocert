#ifndef _COMMON_H
#define _COMMON_H

#include <cassert>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <iomanip>
#include <random>
#include <algorithm>
#include <map>
#include <unordered_set>
#include <memory>
#include <ctime>

#ifndef NDEBUG
#define DBG(X) X
#else
#define DBG(X)
#endif

using permutation = std::vector<unsigned>;

permutation initial_permutation(unsigned n)
{
  permutation p;
  p.resize(n);
  for(unsigned i = 0; i < n; i++)
    p[i] = i;
  return p;
}

permutation operator ~ (const permutation & p)
{
  permutation ret;
  ret.resize(p.size());
  for(unsigned i = 0; i < p.size(); i++)
    ret[p[i]] = i;
  return ret;
}

permutation operator * (const permutation & p1, const permutation & p2)
{
  permutation ret;
  ret.resize(p1.size());
  for(unsigned i = 0; i < p1.size(); i++)
    ret[i] = p1[p2[i]];

  return ret;
}

void shuffle_permutation(permutation & p)
{
  std::mt19937 g(time(0));
  std::shuffle(p.begin(), p.end(), g);  
}

permutation random_permutation(unsigned n)
{
  permutation p = initial_permutation(n);
  shuffle_permutation(p);
  return p;
}


std::ostream & operator << (std::ostream & ostr, const permutation & p)
{
  for(unsigned i = 0; i < p.size(); i++)
    ostr << p[i] << " ";
  return ostr;
}

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

  unsigned num_edges() const
  {
    unsigned c = 0;
    for(unsigned i = 0; i < num_nodes(); i++)
      for(unsigned j = 0; j < num_nodes(); j++)
	if(edge_exists(i, j))
	  c++;
    return c;
  }
  
  void export_dimacs(std::ostream & ostr) const
  {
    ostr << "p edge " << num_nodes() << " " << num_edges() << std::endl;
    for(unsigned i = 0; i < num_nodes(); i++)
      for(unsigned j = 0; j < num_nodes(); j++)
	if(edge_exists(i, j))
	  ostr << "e " << i + 1 << " "  << j + 1 << std::endl;    
  }
  
  void in(std::istream & istr)
  {
    std::string line;
    unsigned n = 0, m = 0;
    unsigned line_count = 0;
    while(std::getline(istr, line))
      {
	line_count++;
	std::stringstream sstr(line);
	std::string first_word;
	sstr >> first_word;
	if(!sstr)
	  {
	    // Empty lines ignored
	    continue;
	  }       
	else if(first_word == "c")
	  {
	    // Ignore comment lines
	    continue;
	  }
	else if(first_word == "p")
	  {
	    std::string second_word;
	    sstr >> second_word;
	    if(!sstr || second_word != "edge")
	      {
		std::cerr << "error reading file (line " << line_count << "): 'edge' expected after 'p'" << std::endl;
		exit(1);
	      }
	    
	    sstr >> n >> m;
	    if(!sstr)
	      {
		std::cerr << "error reading file (line " << line_count << "):  number of nodes or edges missing (or badly formatted)" << std::endl;
		exit(1);
	      }

	    std::string rest;
	    sstr >> rest;
	    if(!rest.empty())
	      {
		std::cerr << "error reading file (line " << line_count << "): bad format (possibly some garbage after the number of edges)" << std::endl;
		exit(1);
	      }
	    reset(n);	    
	  }
	else if(first_word == "e")
	  {
	    if(m == 0 || n == 0)
	      {
		std::cerr << "error reading file (line " << line_count << "): 'p edge n m' line missing" << std::endl;
		exit(1);
	      }
	    
	    unsigned i, j;
	    sstr >> i >> j;
	    if(!sstr)
	      {
		std::cerr << "error reading file (line " << line_count << "): edge vertices not given (or badly formatted)" << std::endl;
		exit(1);
	      }
	    if(i > n || j > n)
	      {
		std::cerr << "error reading file (line " << line_count << "): edge vertices are invalid (greater than the total number of vertices)" << std::endl;
		exit(1);
	      }
	    std::string rest;
	    sstr >> rest;
	    if(!rest.empty())
	      {
		std::cerr << "error reading file (line " << line_count << "): bad format (possibly some garbage after the edge vertices)" << std::endl;
		exit(1);
	      }

	    add_edge(i-1,j-1);
	  }
	else
	  {
	    std::cerr << "error reading file (line " << line_count << "): unknown line type: " << first_word << std::endl;
	    exit(1);
	  }	
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

  
  coloring(std::vector<unsigned> && node_colors, unsigned num_of_colors, unsigned invariant)
    :_node_colors(std::move(node_colors)),
     _cells(num_of_colors),
     _invariant(invariant)    
  {
    for(unsigned i = 0; i < _node_colors.size(); i++)
      {
	_cells[_node_colors[i]].push_back(i);
      }
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

template<typename T>
void print_vector(const std::vector<T> & v)
{
  for(const auto & x : v)
    std::cout << x << ", ";
  std::cout << std::endl;
}


void write_utf8(unsigned code, std::ostream & ostr)
{
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
  ostr.write(buff, count);
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
