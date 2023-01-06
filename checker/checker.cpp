#include "common.hpp"
#include "trie.hpp"
#include "hash_database.hpp"
#include "mem_mapper.hpp"
#include <unistd.h>
#include <signal.h>

std::vector<unsigned> individualize(const std::vector<unsigned> & pi, unsigned v)
{
  unsigned v_color = pi[v];
  std::vector<unsigned> pi_ind(pi.size());
  for(unsigned i = 0; i < pi.size(); i++)
    pi_ind[i] = pi[i] >= v_color ? pi[i] + 1 : pi[i];
  pi_ind[v] = v_color;
  return pi_ind;
}

bool is_discrete(const std::vector<unsigned> & pi)
{
  std::vector<unsigned> counters(pi.size());
  for(unsigned i = 0; i < pi.size(); i++)
    {
      if(++counters[pi[i]] > 1)
	return false;
    }
  return true;  
}

bool is_splitter(const graph & g, const coloring & c, unsigned i)
{
  const std::vector<std::vector<unsigned>> & cells = c.cells();
  const std::vector<unsigned> & cell_i = cells[i];
  
  for(unsigned k = 0; k < cells.size(); k++)
    {
      const std::vector<unsigned> & curr_cell = cells[k];
      
      if(curr_cell.size() == 1)
	continue;

      unsigned saved_count = (unsigned)(-1);

      for(unsigned j = 0; j < curr_cell.size(); j++)
	{
	  unsigned vp = curr_cell[j];
	  unsigned count_edges = 0;
	  for(unsigned l = 0; l < cell_i.size(); l++)
	    {
	      unsigned vs = cell_i[l];
	      if(g.edge_exists(vp, vs))
		count_edges++;
	    }

	  if(saved_count == (unsigned)(-1))
	    saved_count = count_edges;
	  else if(saved_count != count_edges)
	    return true;
	}	    
    }
  return false;
}

unsigned find_first_splitter(const graph & g, const coloring & c)
{
  for(unsigned j = 0; j < c.cells().size(); j++)
    {
      if(is_splitter(g, c, j))      
	return j;
    }
  return (unsigned)(-1);
}


coloring split(const graph & g, const coloring & c, unsigned i)
{
  const std::vector<std::vector<unsigned>> & cells = c.cells();
  const std::vector<unsigned> & cell_i = cells[i];

  std::vector<std::vector<unsigned>> new_cells;
  
  for(unsigned k = 0; k < cells.size(); k++)
    {
      const std::vector<unsigned> & curr_cell = cells[k];
      
      if(curr_cell.size() == 1)
	{
	  new_cells.push_back(curr_cell);
	  continue;
	}

      std::map<unsigned, std::vector<unsigned>> count_map;

      for(unsigned j = 0; j < curr_cell.size(); j++)
	{
	  unsigned vp = curr_cell[j];
	  unsigned count_edges = 0;
	  for(unsigned l = 0; l < cell_i.size(); l++)
	    {
	      unsigned vs = cell_i[l];
	      if(g.edge_exists(vp, vs))
		count_edges++;
	    }
	  count_map[count_edges].push_back(vp);
	}
	    
      unsigned max_cell_size = 0;
      unsigned max_key = 0;
      for(const auto & p : count_map)
	{
	  if(p.second.size() > max_cell_size)
	    {
	      max_cell_size = p.second.size();
	      max_key = p.first;
	    }
	}
	    
      for(auto & p : count_map)
	{
	  if(p.first == max_key)
	    continue;
		
	  new_cells.push_back(std::move(p.second));		
	}

      std::vector<unsigned> & max_cell = count_map[max_key];	      
      new_cells.push_back(std::move(max_cell));
    }
  return coloring(std::move(new_cells), c.num_nodes(), g);
}

const std::vector<unsigned> & first_non_singleton(const coloring & c, unsigned & i)
{
  static const std::vector<unsigned> dummy;
  const std::vector<std::vector<unsigned>> & cells = c.cells();

  for(i = 0; i < cells.size(); i++)
    if(cells[i].size() > 1)
      return cells[i];
  
  i = (unsigned)(-1);
  return dummy;
}


bool canonical_form_derived = false;
graph * gcp = nullptr;

class convert_to_sequence {
private:
  enum class fact_type {
    IS_NODE,
    COLORING_EQUAL,
    COLORING_FINER,
    TARGET_CELL,
    SIGMA_AUTH,
    ORBIT_SUBSET,
    INVARIANTS_EQUAL,
    PRUNED,
    ON_PATH,
    CANONICAL
  };
  static std::vector<unsigned>  _buffer;
public:

  static std::vector<unsigned> && is_node(const std::vector<unsigned> & v)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::IS_NODE);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && is_node(const std::vector<unsigned> & v, unsigned x)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back(x);
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::IS_NODE);
    return std::move(_buffer);
    
  }
  
  static std::vector<unsigned> && coloring_equal(const std::vector<unsigned> & v, const std::vector<unsigned> & pi)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(pi.begin(), pi.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::COLORING_EQUAL);
    return std::move(_buffer);
  }
  
  static std::vector<unsigned> && coloring_finer(const std::vector<unsigned> & v, const std::vector<unsigned> & pi)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(pi.begin(), pi.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::COLORING_FINER);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && coloring_finer(const std::vector<unsigned> & v, unsigned w, const std::vector<unsigned> & pi)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back(w);
    _buffer.push_back((unsigned)(-1));
    std::copy(pi.begin(), pi.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::COLORING_FINER);
    return std::move(_buffer);
  }

  
  static std::vector<unsigned> && target_cell(const std::vector<unsigned> & v, const std::vector<unsigned> & w)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(w.begin(), w.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::TARGET_CELL);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && sigma_auth(const std::vector<unsigned> & sigma)
  {
    _buffer.clear();
    std::copy(sigma.begin(), sigma.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::SIGMA_AUTH);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && orbit_subset(const std::vector<unsigned> & omega, const std::vector<unsigned> & v)
  {
    _buffer.clear();
    std::copy(omega.begin(), omega.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::ORBIT_SUBSET);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && invariants_equal(const std::vector<unsigned> & v, const std::vector<unsigned> & w)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(w.begin(), w.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::INVARIANTS_EQUAL);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && invariants_equal_m(const std::vector<unsigned> & v, const std::vector<unsigned> & w)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end() - 1, std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(w.begin(), w.end() - 1, std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::INVARIANTS_EQUAL);
    return std::move(_buffer);
  }

  
  static std::vector<unsigned> && pruned(const std::vector<unsigned> & v)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::PRUNED);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && pruned(const std::vector<unsigned> & v, unsigned w)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back(w);
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::PRUNED);
    return std::move(_buffer);
  }

  
  static std::vector<unsigned> && on_path(const std::vector<unsigned> & v)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::ON_PATH);
    return std::move(_buffer);
  }

  static std::vector<unsigned> && on_path(const std::vector<unsigned> & v, unsigned w)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back(w);
    _buffer.push_back((unsigned)(-1));
    _buffer.push_back((unsigned)fact_type::ON_PATH);
    return std::move(_buffer);
  }

  
  static std::vector<unsigned> && canonical(const std::vector<unsigned> & v, const std::vector<unsigned> & pi)
  {
    _buffer.clear();
    std::copy(v.begin(), v.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));
    std::copy(pi.begin(), pi.end(), std::back_inserter(_buffer));
    _buffer.push_back((unsigned)(-1));    
    _buffer.push_back((unsigned)fact_type::CANONICAL);
    return std::move(_buffer);
  }
};

std::vector<unsigned>  convert_to_sequence::_buffer;

#ifdef _PREFIX_TREE
using fact_database_t = trie<unsigned>;
#else 
using fact_database_t = hash_database<unsigned>;
#endif

class rule {
protected:
  const graph & _g;
  const coloring & _pi0;
  static unsigned long _counter;
public:
  rule(const graph & g, const coloring & pi0)
    :_g(g),
     _pi0(pi0)
  {
    ++_counter;
  }

  static unsigned long counter()
  {
    return _counter;
  }
  
  virtual void out(std::ostream & ostr) const = 0;
  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const = 0;
  virtual ~rule() {}
  
};

unsigned long rule::_counter = 0UL;

class coloring_axiom_rule : public rule {
public:
  coloring_axiom_rule(const graph & g, const coloring & pi0)
    :rule(g, pi0)
  {}
  virtual void out(std::ostream & ostr) const
  {
    ostr << "ColoringAxiom: [|  |] ==> " << _pi0 << " --> R(G,pi0,[]),  [] in T(G,pi0)" << std::endl;
  }
  
  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    fd.add_sequence(convert_to_sequence::coloring_finer({}, _pi0.node_colors()));
    fd.add_sequence(convert_to_sequence::is_node({}));		    
    return true;
  }
  
};

class individualize_rule : public rule {
private:
  std::vector<unsigned> _p;
  unsigned _v;
  std::vector<unsigned> _pi;
public:
  individualize_rule(const graph & g, const coloring & pi0,
		     std::vector<unsigned> && p,
		     unsigned v,
		     std::vector<unsigned> && pi)
    :rule(g,pi0),
     _p(std::move(p)),
     _v(v),
     _pi(std::move(pi))
  {}

  virtual void out(std::ostream & ostr) const
  {
    ostr << "Individualize: [| R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])=";
    ostr << coloring(std::vector<unsigned>(_pi), _g) << ", [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << _v << "] in T(G,pi0) |] ==> " << coloring(individualize(_pi, _v), _g) << " --> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << _v << "])" << std::endl;    
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_p, _pi)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::is_node(_p, _v)))
      {
	error_message = "Second premise not proved!";
	return false;
      }
    
    fd.add_sequence(convert_to_sequence::coloring_finer(_p, _v, individualize(_pi, _v)));
    return true;
  }
  
};


class split_coloring_rule : public rule {
private:
  std::vector<unsigned> _p;
  std::vector<unsigned> _pi;
  
public:
  split_coloring_rule(const graph & g, const coloring & pi0,
		      std::vector<unsigned> && p,
		      std::vector<unsigned> && pi)
    :rule(g,pi0),
     _p(std::move(p)),
     _pi(std::move(pi))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    coloring c(std::vector<unsigned>(_pi), _g);
    ostr << "SplitColoring: [| " << c << " --> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";

    unsigned m = find_first_splitter(_g, c);
    
    ostr << "]) |] ==> " << split(_g, c, m) << " --> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";    
    ostr << "]) (for: i=" << m << ")" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::coloring_finer(_p, _pi)))
      {
	error_message = "Premise not proved!";
	return false;
      }

    coloring c(std::vector<unsigned>(_pi), _g);
    unsigned i = find_first_splitter(_g, c);
    if(i == (unsigned)(-1))
      {
	error_message = "There is no splitter!";
	return false;
      }
    fd.add_sequence(convert_to_sequence::coloring_finer(_p, split(_g, c, i).node_colors()));
    return true;
  }

  
};

class equitable_rule : public rule {
  std::vector<unsigned> _p;
  std::vector<unsigned> _pi;
public:
  equitable_rule(const graph & g, const coloring & pi0,
		 std::vector<unsigned> && p,
		 std::vector<unsigned> && pi)
    :rule(g,pi0),
     _p(std::move(p)),
     _pi(std::move(pi))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    coloring c(std::vector<unsigned>(_pi), _g);
    ostr << "Equitable: [| " << c << " --> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) |] ==> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) = " << c << std::endl; 
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::coloring_finer(_p, _pi)))
      {
	error_message = "Premise not proved!";
	return false;
      }

    if(find_first_splitter(_g, coloring(std::vector<unsigned>(_pi), _g)) != (unsigned)(-1))
      {
	error_message = "Not equitable!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::coloring_equal(_p, _pi));
    return true;
  }

};

class target_cell_rule : public rule {
  std::vector<unsigned> _p;
  std::vector<unsigned> _pi;
public:
  target_cell_rule(const graph & g, const coloring & pi0,
		   std::vector<unsigned> && p,
		   std::vector<unsigned> && pi)
    :rule(g,pi0),
     _p(std::move(p)),
     _pi(std::move(pi))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "TargetCell: [| R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    coloring c(std::vector<unsigned>(_pi), _g);
    ostr << "]) = " << c << " |] ==> T(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) = {";
    unsigned s = 0;
    const std::vector<unsigned> & fns = first_non_singleton(c, s);
    for(unsigned i = 0; i < fns.size(); i++)
      ostr << fns[i] << " ";
    ostr << "} (for: i = " << s << "), ";
    for(unsigned i = 0; i < fns.size(); i++)
      {
	ostr << "[";
	for(unsigned j = 0; j < _p.size(); j++)
	  ostr << _p[j] << " ";
	ostr << fns[i] << "] in T(G,pi0)";
	if (i != fns.size() - 1)
	  ostr << ",";
      }
    ostr << std::endl;
  }
  
  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_p, _pi)))
      {
	error_message = "Premise not proved!";
	return false;
      }

    unsigned s = 0;
    coloring c(std::vector<unsigned>(_pi), _g);
    const std::vector<unsigned> & fns = first_non_singleton(c, s);
    if(s == (unsigned)(-1))
      {
	error_message = "No non-singleton cells!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::target_cell(_p, fns));

    for(unsigned i = 0; i < fns.size(); i++)
      fd.add_sequence(convert_to_sequence::is_node(_p, fns[i])); 
    
    return true;
  }

};

class invariant_axiom_rule : public rule {
private:
  std::vector<unsigned> _p;
public:
  invariant_axiom_rule(const graph & g, const coloring & pi0,
		       std::vector<unsigned> && p)
    :rule(g, pi0),
     _p(std::move(p))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "InvariantAxiom: [| [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "] in T(G,pi0) |] ==> fi(G,pi0, [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) = fi(G,pi0, [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])" << std::endl;    
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::is_node(_p)))
      {
	error_message = "Premise not proved!";
	return false;
      }
    
    fd.add_sequence(convert_to_sequence::invariants_equal(_p, _p));
    return true;
  }

};

class invariants_equal_rule : public rule {
private:
  std::vector<unsigned> _vp;
  std::vector<unsigned> _pi1;
  std::vector<unsigned> _wp;
  std::vector<unsigned> _pi2;
public:
  invariants_equal_rule(const graph & g, const coloring & pi0,
			std::vector<unsigned> && vp,
			std::vector<unsigned> && pi1,
			std::vector<unsigned> && wp,
			std::vector<unsigned> && pi2)
    :rule(g,pi0),
     _vp(std::move(vp)),
     _pi1(std::move(pi1)),
     _wp(std::move(wp)),
     _pi2(std::move(pi2))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "InvariantsEqual: [| fi(G,pi0,[";
    for(unsigned i = 0; i < _vp.size() - 1; i++)
      ostr << _vp[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _wp.size() - 1; i++)
      ostr << _wp[i] << " ";
    ostr << "]), R(G,pi0,[";
    for(unsigned i = 0; i < _vp.size(); i++)
      ostr << _vp[i] << " ";
    coloring c1(std::vector<unsigned>(_pi1),_g);
    ostr << "]) = " << c1 << ", R(G,pi0,[";
    for(unsigned i = 0; i < _wp.size(); i++)
      ostr << _wp[i] << " ";
    coloring c2(std::vector<unsigned>(_pi2),_g);
    ostr << "]) = " << c2 << " |] ==> fi(G,pi0,[";
    for(unsigned i = 0; i < _vp.size(); i++)
      ostr << _vp[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _wp.size(); i++)
      ostr << _wp[i] << " ";
    ostr << "])" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::invariants_equal_m(_vp, _wp)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_vp, _pi1)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_wp, _pi2)))
      {
	error_message = "Third premise not proved!";
	return false;
      }
    
    if(coloring(std::vector<unsigned>(_pi1), _g, true).invariant() !=
       coloring(std::vector<unsigned>(_pi2), _g, true).invariant())
      {
	error_message = "Invariants not equal!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::invariants_equal(_vp, _wp));
    return true;
  }

};


class invariants_equal_sym_rule : public rule {
private:
  std::vector<unsigned> _vp;
  std::vector<unsigned> _wp;
public:
  invariants_equal_sym_rule(const graph & g, const coloring & pi0,
			    std::vector<unsigned> && vp,
			    std::vector<unsigned> && wp)
    :rule(g,pi0),
     _vp(std::move(vp)),
     _wp(std::move(wp))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "InvariantsEqualSym: [| fi(G,pi0,[";
    for(unsigned i = 0; i < _vp.size(); i++)
      ostr << _vp[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _wp.size(); i++)
      ostr << _wp[i] << " ";
    ostr << "]) |] ==> fi(G,pi0,[";
    for(unsigned i = 0; i < _wp.size(); i++)
      ostr << _wp[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _vp.size(); i++)
      ostr << _vp[i] << " ";
    ostr << "])" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::invariants_equal(_vp, _wp)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::invariants_equal(_wp, _vp));
    return true;
  }

};




class orbits_axiom_rule : public rule {
private:
  unsigned _v;
  std::vector<unsigned> _p;
public:
  orbits_axiom_rule(const graph & g, const coloring & pi0,
		    unsigned v,
		    std::vector<unsigned> && p)
    :rule(g,pi0),
     _v(v),
     _p(std::move(p))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "OrbitsAxiom: [| [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "] in T(G,pi0) |] ==> { " << _v << " } <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::is_node(_p)))
      {
	error_message = "Premise not proved!";
	return false;
      }
    
    if(_v >= _g.num_nodes())
      {
	error_message = "Given vertex is not a vertex of G!";
	return false;
      }
    
    fd.add_sequence(convert_to_sequence::orbit_subset({_v}, _p));
    return true;
  }
  
};

class merge_orbits_rule : public rule {
private:
  std::vector<unsigned> _o1;
  std::vector<unsigned> _o2;
  std::vector<unsigned> _p;
  permutation _sigma;
  unsigned _w1;
  unsigned _w2;
public:
  merge_orbits_rule(const graph & g, const coloring & pi0,
		    std::vector<unsigned> && o1,
		    std::vector<unsigned> && o2,
		    std::vector<unsigned> && p,
		    permutation && sigma,
		    unsigned w1,
		    unsigned w2)
    :rule(g,pi0),
     _o1(std::move(o1)),
     _o2(std::move(o2)),
     _p(std::move(p)),
     _sigma(std::move(sigma)),
     _w1(w1),
     _w2(w2)
  {}
  

  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "MergeOrbits: [| {";
    for(unsigned i = 0; i < _o1.size(); i++)
      ostr << _o1[i] << " ";
    ostr << "} <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]), {";
    for(unsigned i = 0; i < _o2.size(); i++)
      ostr << _o2[i] << " ";
    ostr << "} <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) |] ==> {";
    std::vector<unsigned> res;
    std::merge(_o1.begin(), _o1.end(), _o2.begin(), _o2.end(), std::back_inserter(res)); 
    auto it = std::unique(res.begin(), res.end()); // probably unnecessary   
    res.resize(std::distance(res.begin(), it));    
    
    for(unsigned i = 0; i < res.size(); i++)
      ostr << res[i] << " ";
    ostr << "} <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) (for: sigma = <";
    for(unsigned i = 0; i < _sigma.size(); i++)
      ostr << _sigma[i] << " ";
    ostr << ">, w1 = " << _w1 << ", w2 = " << _w2 << ")" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::orbit_subset(_o1,_p)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::orbit_subset(_o2,_p)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    std::vector<unsigned> sigma_seq = convert_to_sequence::sigma_auth(_sigma);
    if(!fd.sequence_exists(sigma_seq))
      {
	if(!_g.is_automorphism(_sigma) || !_pi0.is_automorphism(_sigma))
	  {
	    error_message = "Permutation is not an automorphism!";
	    return false;
	  }
	else
	  fd.add_sequence(std::move(sigma_seq));
      }
    
    for(unsigned i = 0; i < _p.size(); i++)
      {
	if(_sigma[_p[i]] != _p[i])
	  {
	    error_message = "Permutation is not pointwise stabilizing for the sequence!";
	    return false;	    
	  }
      }

    if(std::find(_o1.begin(), _o1.end(), _w1) == _o1.end())
      {
	error_message = "w1 does not belong to O1!";
	return false;
      }

    if(std::find(_o2.begin(), _o2.end(), _w2) == _o2.end())
      {
	error_message = "w2 does not belong to O2!";
	return false;
      }

    if(_sigma[_w1] != _w2)
      {
	error_message = "Permutation does not merge orbits";
	return false;
      }

    std::vector<unsigned> res;
    std::merge(_o1.begin(), _o1.end(), _o2.begin(), _o2.end(), std::back_inserter(res));
    auto it = std::unique(res.begin(), res.end()); // probably unnecessary
    res.resize(std::distance(res.begin(), it));
    fd.add_sequence(convert_to_sequence::orbit_subset(res, _p));	       	       
    return true;
  }

};

class prune_invariant_rule : public rule {
private:
  std::vector<unsigned> _v;
  std::vector<unsigned> _pi1;
  std::vector<unsigned> _w;
  std::vector<unsigned> _pi2;
public:
  prune_invariant_rule(const graph & g, const coloring & pi0,
		       std::vector<unsigned> && v,
		       std::vector<unsigned> && pi1,
		       std::vector<unsigned> && w,
		       std::vector<unsigned> && pi2)
    :rule(g, pi0),
     _v(std::move(v)),
     _pi1(std::move(pi1)),
     _w(std::move(w)),
     _pi2(std::move(pi2))
  {}
  		       
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PruneInvariant: [| fi(G,pi0,[";
    for(unsigned i = 0; i < _v.size() - 1; i++)
      ostr << _v[i] << " ";
    ostr << "]) = fi(G,pi0, [";
    for(unsigned i = 0; i < _w.size() - 1; i++)
      ostr << _w[i] << " ";
    ostr << "]), R(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) = " << coloring(std::vector<unsigned>(_pi1),_g) << ", R(G, pi0, [";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "]) = " << coloring(std::vector<unsigned>(_pi2),_g) << " |] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "])" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::invariants_equal_m(_v, _w)))
      {
	error_message = "First premise not proved!";
	return false;	
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_v, _pi1)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_w, _pi2)))
      {
	error_message = "Third premise not proved!";
	return false;
      }

    if(coloring(std::vector<unsigned>(_pi1), _g, true).invariant() <=
       coloring(std::vector<unsigned>(_pi2), _g, true).invariant())
      {
	error_message = "First invariant not greater!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::pruned(_w));    
    return true;
  }

};

class prune_leaf_rule : public rule {
private:
  std::vector<unsigned> _v;
  std::vector<unsigned> _pi1;
  std::vector<unsigned> _w;
  std::vector<unsigned> _pi2;
public:
  prune_leaf_rule(const graph & g, const coloring & pi0,
		  std::vector<unsigned> && v,
		  std::vector<unsigned> && pi1,
		  std::vector<unsigned> && w,
		  std::vector<unsigned> && pi2)
    :rule(g, pi0),
     _v(std::move(v)),
     _pi1(std::move(pi1)),
     _w(std::move(w)),
     _pi2(std::move(pi2))
  {}

  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PruneLeaf: [| R(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) = " << coloring(std::vector<unsigned>(_pi1), _g) << ", R(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "]) = " << coloring(std::vector<unsigned>(_pi2), _g) << ", fi(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "]) |] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "])" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_v, _pi1)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_w, _pi2)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::invariants_equal(_v, _w)))
      {
	error_message = "Third premise not proved!";
	return false;	
      }

    if(!is_discrete(_pi2))
      {
	error_message = "Second coloring not discrete!";
	return false;
      }

        
    if(is_discrete(_pi1))
      {        
	if(_g.apply_permutation(_pi1).compare_to(_g.apply_permutation(_pi2)) <= 0)
	  {
	    error_message = "First coloring discrete, but first graph not greater!";
	    return false;
	  }
      }

    fd.add_sequence(convert_to_sequence::pruned(_w));    
    return true;
  }

};

class prune_automorphism_rule : public rule {
  std::vector<unsigned> _v;
  std::vector<unsigned> _w;
  permutation _sigma;
  
public:
  prune_automorphism_rule(const graph & g, const coloring & pi0,
			  std::vector<unsigned> && v,
			  std::vector<unsigned> && w,
			  permutation && sigma)
    :rule(g,pi0),
     _v(std::move(v)),
     _w(std::move(w)),
     _sigma(std::move(sigma))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PruneAutomorphism: [| [";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "] in T(G,pi0), [";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "] in T(G,pi0) |] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "]) (for: sigma = <";
    for(unsigned i = 0; i < _sigma.size(); i++)
      ostr << _sigma[i] << " ";
    ostr << ">)" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::is_node(_v)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::is_node(_w)))
      {
	error_message = "Second premise not proved!";
	return false;
      }
    
    if(_v >= _w)
      {
	error_message = "First sequence is not lexicographically smaller!";
	return false;
      }

    std::vector<unsigned> sigma_seq = convert_to_sequence::sigma_auth(_sigma);
    if(!fd.sequence_exists(sigma_seq))
      {
	if(!_g.is_automorphism(_sigma) || !_pi0.is_automorphism(_sigma))
	  {
	    error_message = "Permutation is not an automorphism!";
	    return false;
	  }
	else
	  fd.add_sequence(std::move(sigma_seq));
      }

       
    for(unsigned i = 0; i < _v.size(); i++)
      {
	if(_sigma[_v[i]] != _w[i])
	  {
	    error_message = "First sequence is not translated to second by sigma!";
	    return false;
	  }
      }

    fd.add_sequence(convert_to_sequence::pruned(_w));
    return true;
  }
  
};

class prune_orbits_rule : public rule {
public:
  std::vector<unsigned> _omega;
  std::vector<unsigned> _v;
  unsigned _w1;
  unsigned _w2;
public:
  prune_orbits_rule(const graph & g, const coloring & pi0,
		    std::vector<unsigned> && omega,
		    std::vector<unsigned> && v,
		    unsigned w1,
		    unsigned w2)
    :rule(g,pi0),
     _omega(std::move(omega)),
     _v(std::move(v)),
     _w1(w1),
     _w2(w2)
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PruneOrbits: [| [";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << _w1 << "] in T(G,pi0), [";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << _w2 << "] in T(G,pi0), {";
    for(unsigned i = 0; i < _omega.size(); i++)
      ostr << _omega[i] << " ";
    ostr << "} <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) |] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << _w2 << "]) (for w1 = " << _w1 << ")" << std::endl;    
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {

    if(!fd.sequence_exists(convert_to_sequence::is_node(_v, _w1)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::is_node(_v, _w2)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    
    if(!fd.sequence_exists(convert_to_sequence::orbit_subset(_omega, _v)))
      {
	error_message = "Third premise not proved!";
	return false;
      }

    if(std::find(_omega.begin(), _omega.end(), _w2) == _omega.end())
      {
	error_message = "w2 not in Omega!";
	return false;
      }

    if(std::find(_omega.begin(), _omega.end(), _w1) == _omega.end())
      {
	error_message = "w1 not in Omega!";
	return false;
      }

    if(_w1 >= _w2)
      {
	error_message = "w1 >= w2!";
	return false;
      }

    fd.add_sequence(convert_to_sequence::pruned(_v, _w2));           
    return true;
  }

};

class prune_parent_rule : public rule {
private:
  std::vector<unsigned> _v;
  std::vector<unsigned> _w;
public:
  prune_parent_rule(const graph & g, const coloring & pi0,
		    std::vector<unsigned> && v,
		    std::vector<unsigned> && w)
    :rule(g,pi0),
     _v(std::move(v)),
     _w(std::move(w))
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PruneParent: [| T(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) = {";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "},";
    for(unsigned i = 0; i < _w.size(); i++)
      {
	ostr << "pruned(G,pi0,[";
	for(unsigned j = 0; j < _v.size(); j++)
	  ostr << _v[j] << " ";
	ostr << _w[i] << "]), ";       
      }
    ostr << " |] ==> pruned(G,pi0,[";
    for(unsigned j = 0; j < _v.size(); j++)
      ostr << _v[j] << " ";
    ostr << "])" << std::endl;      
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::target_cell(_v, _w)))
      {
	error_message = "First premise not proved!";
	return false;	
      }

    for(unsigned i = 0; i < _w.size(); i++)
      {
	if(!fd.sequence_exists(convert_to_sequence::pruned(_v, _w[i])))
	  {
	    error_message = "One of the 'pruned' premises not proved!";
	    return false;
	  }
      }

    fd.add_sequence(convert_to_sequence::pruned(_v));
    return true;
  }

};

class path_axiom_rule : public rule {  
public:
  path_axiom_rule(const graph & g, const coloring & pi0)
    :rule(g,pi0)
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "PathAxiom: [| |] ==> on_path(G,pi0,[])" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    fd.add_sequence(convert_to_sequence::on_path({}));    
    return true;
  }
  
};

class extend_path_rule : public rule {
private:
  std::vector<unsigned> _v;
  std::vector<unsigned> _w;
  unsigned _w_max;
public:
  extend_path_rule(const graph & g, const coloring & pi0,
		   std::vector<unsigned> && v,
		   std::vector<unsigned> && w,
		   unsigned w_max)
    :rule(g,pi0),
     _v(std::move(v)),
     _w(std::move(w)),
     _w_max(w_max)
  {}
  
  virtual void out(std::ostream & ostr) const
  {
    ostr << "ExtendPath: [| on_path(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]), T(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]) = {";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "},";
    for(unsigned i = 0; i < _w.size(); i++)
      {
	if(_w[i] == _w_max)
	  continue;

	ostr << "pruned(G,pi0,[";
	for(unsigned j = 0; j < _v.size(); j++)
	  ostr << _v[j] << " ";
	ostr << _w[i] << "]),";

      }
    ostr << " |] ==> on_path(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << _w_max << "])" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::on_path(_v)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::target_cell(_v, _w)))
      {
	error_message = "Second premise not proved!";
	return false;
      }
    
    bool w_max_found = false;
    for(unsigned i = 0; i < _w.size(); i++)
      {
	if(_w[i] == _w_max)
	  {
	    w_max_found = true;
	    continue;
	  }
	if(!fd.sequence_exists(convert_to_sequence::pruned(_v, _w[i])))
	  {
	    //std::cerr << "PRUNED PREMISE: " << i << " NOT PROVED (MAX: " << _w_max << ")" << std::endl;
	    error_message = "One of 'pruned' premises not proved!";
	    return false;
	  }
      }

    if(!w_max_found)
      {
	error_message = "Vertex not in W!";
	return false;
      }
    
    fd.add_sequence(convert_to_sequence::on_path(_v, _w_max));    
    return true;
  }

};

class canonical_leaf_rule : public rule {
private:
  std::vector<unsigned> _v;
  std::vector<unsigned> _pi;
public:
  canonical_leaf_rule(const graph & g, const coloring & pi0,
		      std::vector<unsigned> && v,
		      std::vector<unsigned> && pi)
    :rule(g,pi0),
     _v(std::move(v)),
     _pi(std::move(pi))
  {}
  virtual void out(std::ostream & ostr) const
  {
    ostr << "CanonicalLeaf: [| on_path(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]), R(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    coloring pi(std::vector<unsigned>(_pi), _g);
    ostr << "]) = " << pi << " |] ==> C(G,pi0) = (G^pi,pi0^pi) (for: pi = " << pi << ")" << std::endl;    
  }
  
  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::on_path(_v)))
      {
	error_message = "First premise not proved!";
	return false;
      }

    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_v, _pi)))
      {
	error_message = "Second premise not proved!";
	return false;
      }

    if(!is_discrete(_pi))
      {
	error_message = "Coloring not discrete!";
	return false;
      }

    canonical_form_derived = true;
    if(gcp != nullptr)
      *gcp = _g.apply_permutation(_pi); 
    fd.add_sequence(convert_to_sequence::canonical(_v, _pi));
    return true;
  }
  
};



using rule_ptr = std::shared_ptr<const rule>;

inline
std::ostream & operator << (std::ostream & ostr, const rule_ptr & r)
{
  r->out(ostr);
  return ostr;
}

template <typename T>
void read_sequence(T & istr, std::vector<unsigned> & s)
{
  unsigned size = read_utf8(istr);
  //  std::cout << "SIZE: " << size << std::endl;
  for(unsigned i = 0; i < size; i++)
    s.push_back(read_utf8(istr));
}

template <typename T>
void read_coloring(T & istr, unsigned num_nodes, std::vector<unsigned> & c)
{
  for(unsigned i = 0; i < num_nodes; i++)
    c.push_back(read_utf8(istr));
}

template <typename T>
void read_permutation(T & istr, unsigned num_nodes, std::vector<unsigned> & c)
{
  for(unsigned i = 0; i < num_nodes; i++)
    c.push_back(read_utf8(istr));
}


template <typename T>
rule_ptr read_next_rule(T & istr, const graph & g, const coloring & pi0)
{
  unsigned code;
  while((code = read_utf8(istr)) != (unsigned)(-1))
    {
      if(code == (unsigned)rule_type::COLORING_AXIOM)
	{
	  //	  std::cout << "COLORING AXIOM" << std::endl;
	  
	  return std::make_shared<coloring_axiom_rule>(g, pi0);	  
	}
      else if(code == (unsigned)rule_type::INDIVIDUALIZE)
	{
	  //std::cout << "INDIVIDUALIZE" << std::endl;
	  
	  std::vector<unsigned> v;
	  read_sequence(istr,v);
	  unsigned w;
	  w = read_utf8(istr);
	  std::vector<unsigned> c;
	  read_coloring(istr, g.num_nodes(), c);
	  return std::make_shared<individualize_rule>(g, pi0, std::move(v), w, std::move(c));	  
	}
      else if(code == (unsigned)rule_type::SPLIT_COLORING)
	{
	  // std::cout << "SPLIT_COLORING: " << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c;
	  read_coloring(istr, g.num_nodes(), c);
	  return std::make_shared<split_coloring_rule>(g, pi0, std::move(v), std::move(c));	  
	}
      else if(code == (unsigned)rule_type::EQUITABLE)
	{
	  //std::cout << "EQUITABLE" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c;
	  read_coloring(istr, g.num_nodes(), c);
	  return std::make_shared<equitable_rule>(g,pi0, std::move(v), std::move(c));	  	  
	}
      else if(code == (unsigned)rule_type::TARGET_CELL)
	{
	  //std::cout << "TARGET_CELL" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c;
	  read_coloring(istr, g.num_nodes(), c);
	  return std::make_shared<target_cell_rule>(g, pi0, std::move(v), std::move(c));	  
	}
      else if(code == (unsigned)rule_type::INVARIANT_AXIOM)
	{
	  // std::cout << "INVARIANT_AXIOM" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  return std::make_shared<invariant_axiom_rule>(g, pi0, std::move(v));
	}
      else if(code == (unsigned)rule_type::INVARIANTS_EQUAL)
	{
	  //std::cout << "INVARIANTS_EQUAL" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c1;
	  read_coloring(istr, g.num_nodes(), c1);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  std::vector<unsigned> c2;
	  read_coloring(istr, g.num_nodes(), c2);
	  return std::make_shared<invariants_equal_rule>(g, pi0, std::move(v), std::move(c1),
							 std::move(w), std::move(c2));
	  
	}
      else if(code == (unsigned)rule_type::INVARIANTS_EQUAL_SYM)
	{
	  //std::cout << "INVARIANTS_EQUAL_SYM" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  return std::make_shared<invariants_equal_sym_rule>(g, pi0, std::move(v), std::move(w));	  
	}
      else if(code == (unsigned)rule_type::ORBITS_AXIOM)
	{
	  //std::cout << "ORBITS_AXIOM" << std::endl;
	  unsigned w;
	  w = read_utf8(istr);
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  return std::make_shared<orbits_axiom_rule>(g, pi0, w, std::move(v));
	}
      else if(code == (unsigned)rule_type::MERGE_ORBITS)
	{
	  //std::cout << "MERGE_ORBITS" << std::endl;	  
	  std::vector<unsigned> o1;
	  read_sequence(istr, o1);
	  std::vector<unsigned> o2;
	  read_sequence(istr, o2);
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> sigma;
	  read_permutation(istr, g.num_nodes(), sigma);
	  unsigned w1, w2;
	  w1 = read_utf8(istr);
	  w2 = read_utf8(istr);
	  return std::make_shared<merge_orbits_rule>(g,pi0,std::move(o1),std::move(o2),
						     std::move(v),std::move(sigma),w1,w2);
	}
      else if(code == (unsigned)rule_type::PRUNE_INVARIANT)
	{
	  // std::cout << "PRUNE_INVARIANT" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c1;
	  read_coloring(istr, g.num_nodes(), c1);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  std::vector<unsigned> c2;
	  read_coloring(istr, g.num_nodes(), c2);
	  return std::make_shared<prune_invariant_rule>(g, pi0, std::move(v), std::move(c1),
							std::move(w), std::move(c2));
	}
      else if(code == (unsigned)rule_type::PRUNE_LEAF)
	{
	  //  std::cout << "PRUNE_LEAF" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c1;
	  read_coloring(istr, g.num_nodes(), c1);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  std::vector<unsigned> c2;
	  read_coloring(istr, g.num_nodes(), c2);
	  return std::make_shared<prune_leaf_rule>(g, pi0, std::move(v), std::move(c1), std::move(w),
						   std::move(c2));

	}
      else if(code == (unsigned)rule_type::PRUNE_AUTOMORPHISM)
	{
	  // std::cout << "PRUNE_AUTOMORPHISM" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  std::vector<unsigned> sigma;
	  read_permutation(istr, g.num_nodes(), sigma);
	  return std::make_shared<prune_automorphism_rule>(g, pi0, std::move(v),  std::move(w), std::move(sigma));

	}
      else if(code == (unsigned)rule_type::PRUNE_ORBITS)
	{
	  //std::cout << "PRUNE_ORBITS" << std::endl;
	  std::vector<unsigned> o1;
	  read_sequence(istr, o1);
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  unsigned w1, w2;
	  w1 = read_utf8(istr);
	  w2 = read_utf8(istr);
	  return std::make_shared<prune_orbits_rule>(g, pi0, std::move(o1), std::move(v), w1, w2);
	  
	}
      else if(code == (unsigned)rule_type::PRUNE_PARENT)
	{
	  //std::cout << "PRUNE_PARENT" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  return std::make_shared<prune_parent_rule>(g, pi0, std::move(v), std::move(w));
	}
      else if(code == (unsigned)rule_type::PATH_AXIOM)
	{
	  //std::cout << "PATH_AXIOM" << std::endl;
	  return std::make_shared<path_axiom_rule>(g, pi0);
	}
      else if(code == (unsigned)rule_type::EXTEND_PATH)
	{
	  //std::cout << "EXTEND_PATH" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> w;
	  read_sequence(istr, w);
	  unsigned w_max;
	  w_max = read_utf8(istr);
	  return std::make_shared<extend_path_rule>(g, pi0, std::move(v), std::move(w), w_max);	 	  
	}
      else if(code == (unsigned)rule_type::CANONICAL_LEAF)
	{
	  //std::cout << "CANONICAL_LEAF" << std::endl;
	  std::vector<unsigned> v;
	  read_sequence(istr, v);
	  std::vector<unsigned> c;
	  read_coloring(istr, g.num_nodes(), c);
	  return std::make_shared<canonical_leaf_rule>(g, pi0, std::move(v), std::move(c));
	}
      else
	{
	  std::cerr << "ERROR, UNKNOWN RULE" << std::endl;
	}             
    }
  return nullptr;
}

#ifdef _ENABLE_MMAP
mem_mapper istr;

void handler(int signum)
{
  std::cout << "Progress: " << (unsigned)(istr.curr_position() / (double)istr.file_length() * 100) << "% Rules: " << rule::counter() << std::endl;
  alarm(1);
}

#endif

void check_proof(const graph & g, const coloring & pi0, char * proof_file_path, bool human_readable = false)
{
#ifndef _ENABLE_MMAP
  
  std::ifstream istr(proof_file_path);

  if(!istr)
    {
      std::cerr << "Cannot open file for reading: " << proof_file_path << std::endl;
      exit(1);
    }  
#else
  
  if(!istr.map_file(std::string(proof_file_path)))
    {
      std::cerr << "Cannot map file for reading: " << proof_file_path << std::endl;
      exit(1);
    }
  
  struct sigaction act;
  sigemptyset(&act.sa_mask);
  act.sa_flags = 0;
  act.sa_handler = handler;  
  sigaction(SIGALRM, &act, NULL);
#endif
  
  rule_ptr rp;

  unsigned num_nodes = read_utf8(istr);
  if(num_nodes != g.num_nodes())
    {
      std::cerr << "Graph for which the proof is generated and given graph have different number of nodes (possibly wrong graph file given)!!" << std::endl;
      exit(1);
    }
  
  if(human_readable)
    {      
      while((rp = read_next_rule(istr, g, pi0)).get() != nullptr)
	{     
	  rp->out(std::cout);
	}
      return;
    }
  
  fact_database_t fd;
  std::string error_message;

#ifdef _ENABLE_MMAP 
  alarm(1);
#endif
  
  while((rp = read_next_rule(istr, g, pi0)).get() != nullptr)
    {      
      if(!rp->check_rule(fd, error_message))
	{	
	  rp->out(std::cout);
	  std::cout << "ERROR: " << error_message << std::endl;
	  exit(1);
	}
    }
  
  if(!canonical_form_derived)
    {
      std::cout << "ERROR: Canonical leaf fact not derived!" << std::endl;
      exit(1);
    }
  else
    {
      std::cout << "PROOF OK" << std::endl;
    }

#ifdef _ENABLE_MMAP
  sigemptyset(&act.sa_mask);
  act.sa_flags = 0;
  act.sa_handler = SIG_IGN;  
  sigaction(SIGALRM, &act, NULL);
#endif
}

int main(int argc, char ** argv)
{
  
  if(argc < 3)
    {
      std::cerr << "usage: " << argv[0] << " graph_file proof_file [-h | canon_graph_file | graph2_file proof2_file]" << std::endl;
      std::cerr << std::endl;
      std::cerr << "Examples: " << std::endl;
      std::cerr << "1) The command: " << std::endl;
      std::cerr << "   " << argv[0] << " input_graph.in proof_file.in" << std::endl;
      std::cerr << "checks the proof given in proof_file.in for the graph given in input_graph.in" << std::endl;
      std::cerr << "2) The command: " << std::endl;
      std::cerr << "   " << argv[0] << " input_graph.in proof_file.in -h" << std::endl;
      std::cerr << "prints the proof rules from proof_file.in for the graph given in input_graph.in in a human readable form (for debugging)" << std::endl;
      std::cerr << "3) The command: " << std::endl;
      std::cerr << "   " << argv[0] << " input_graph.in proof_file.in can_graph.in" << std::endl;
      std::cerr << "checks the proof given in proof_file.in for the graph given in input_graph.in, and then compares the derived canonical form with the graph given in can_graph.in" << std::endl;
      std::cerr << "4) The command: " << std::endl;
      std::cerr << "   " << argv[0] << " input_graph1.in proof_file1.in input_graph2.in proof_file2.in" << std::endl;
      std::cerr << "checks the proof given in proof_file{1,2}.in for the graph given in input_graph{1,2}.in, and then compares the derived canonical forms of the two graphs" << std::endl;
      std::cerr << std::endl;
      std::cerr << "All graphs should be given in DIMACS format" << std::endl;
      exit(1);
    }
  
  graph g;
  graph gc;
  
  std::ifstream graph_file(argv[1]);

  if(!graph_file)
    {
      std::cerr << "Cannot open file for reading: " << argv[1] << std::endl;
      exit(1);
    }
  
  graph_file >> g;
  graph_file.close();  
  std::cerr << "Reading graph done" << std::endl;
  coloring pi0(g.num_nodes());

  bool human_readable = false;
  if(argc >= 4)
    {
      if(std::string(argv[3]) == std::string("-h"))
	human_readable = true;
      else
	gcp = &gc;
    }
  check_proof(g, pi0, argv[2], human_readable);

  if(argc == 4 && !human_readable)
    {
      std::ifstream can_ifile(argv[3]);

      if(!can_ifile)
	{
	  std::cerr << "Cannot open file for reading: " << argv[3] << std::endl;
	  exit(1);
	}

      graph igc;
      can_ifile >> igc;
      can_ifile.close();
      if(igc.compare_to(gc) != 0)
	std::cout << "ERROR: Derived canonical graph is different from given canonical form" << std::endl;
      else
	std::cout << "CANONICAL FORM OK" << std::endl;
    }
  else if(argc >= 5 && !human_readable)
    {
      graph g2;
      graph gc2;
      std::ifstream graph2_file(argv[3]);
      if(!graph2_file)
	{
	  std::cerr << "Cannot open file for reading: " << argv[3] << std::endl;
	  exit(1);
	}

      graph2_file >> g2;
      graph2_file.close();
      std::cerr << "Reading second graph done" << std::endl;
      coloring pi2(g2.num_nodes());
      gcp = &gc2;
      canonical_form_derived = false;
      check_proof(g2, pi2, argv[4], false);

      if(gc.compare_to(gc2) != 0)
	std::cout << "Graphs have different canonical forms (NOT isomorphic)" << std::endl;	  	  
      else
	std::cout << "Graphs have equal canonical forms (isomorphic)" << std::endl;
    }
  
  
  return 0;
}
