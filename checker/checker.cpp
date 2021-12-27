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

class convert_to_sequence {
private:
  enum class fact_type {
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

  
  static std::vector<unsigned> && canonical()
  {
    _buffer.clear();
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
    ostr << "ColoringAxiom: [] ==> R(G,pi0,[]) <= " << _pi0 << std::endl;
  }
  
  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    fd.add_sequence(convert_to_sequence::coloring_finer({}, _pi0.node_colors()));
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
    ostr << "Individualize: [R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])=";
    ostr << coloring(std::vector<unsigned>(_pi), _g);
    ostr << "] ==> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << _v << "]) <= ";
    ostr << coloring(individualize(_pi, _v), _g) << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::coloring_equal(_p, _pi)))
      {
	error_message = "Premise not proved!";
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
    ostr << "SplitColoring: [R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    coloring c(std::vector<unsigned>(_pi), _g);
    
    unsigned m = find_first_splitter(_g, c);
    
    ostr << "]) <= " << c << "] ==> R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";    
    ostr << "]) <= " << split(_g, c, m) << " (for: i=" << m << ")" << std::endl;
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
    ostr << "Equitable: [R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    coloring c(std::vector<unsigned>(_pi), _g);
    ostr << "]) <= " << c << "] ==> R(G,pi0,[";
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
    ostr << "TargetCell: R(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    coloring c(std::vector<unsigned>(_pi), _g);
    ostr << "]) = " << c << "] ==> T(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) = {";
    unsigned s = 0;
    const std::vector<unsigned> & fns = first_non_singleton(c, s);
    for(unsigned i = 0; i < fns.size(); i++)
      ostr << fns[i] << " ";
    ostr << "} (for: i = " << s << ")" << std::endl;
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
    ostr << "InvariantAxiom: [] ==> fi(G,pi0, [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "]) = fi(G,pi0, [";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])" << std::endl;    
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
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
    ostr << "InvariantsEqual: [fi(G,pi0,[";
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
    ostr << "]) = " << c2 << "] ==> fi(G,pi0,[";
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
    ostr << "InvariantsEqualSym: [fi(G,pi0,[";
    for(unsigned i = 0; i < _vp.size(); i++)
      ostr << _vp[i] << " ";
    ostr << "]) = fi(G,pi0,[";
    for(unsigned i = 0; i < _wp.size(); i++)
      ostr << _wp[i] << " ";
    ostr << "])] ==> fi(G,pi0,[";
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
    ostr << "OrbitsAxiom: [] ==> { " << _v << " } <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _p.size(); i++)
      ostr << _p[i] << " ";
    ostr << "])" << std::endl;
  }

  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
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
    ostr << "MergeOrbits: [{";
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
    ostr << "])] ==> {";
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
    ostr << "PruneInvariant: [fi(G,pi0,[";
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
    ostr << "]) = " << coloring(std::vector<unsigned>(_pi2),_g) << " ] ==> pruned(G,pi0,[";
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
    ostr << "PruneLeaf: [R(G,pi0,[";
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
    ostr << "])] ==> pruned(G,pi0,[";
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
	    error_message = "First graph not greater!";
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
    ostr << "PruneAutomorphism: [] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _w.size(); i++)
      ostr << _w[i] << " ";
    ostr << "]) (for: v = [";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "], sigma = <";
    for(unsigned i = 0; i < _sigma.size(); i++)
      ostr << _sigma[i] << " ";
    ostr << ">)" << std::endl;
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
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
    ostr << "PruneOrbits: [{";
    for(unsigned i = 0; i < _omega.size(); i++)
      ostr << _omega[i] << " ";
    ostr << "} <| orbits(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "])] ==> pruned(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << _w2 << "]) (for w1 = " << _w1 << ")" << std::endl;    
  }


  virtual bool check_rule(fact_database_t & fd, std::string & error_message) const
  {
    if(!fd.sequence_exists(convert_to_sequence::orbit_subset(_omega, _v)))
      {
	error_message = "Premise not proved!";
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
    ostr << "PruneParent: [T(G,pi0,[";
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
    ostr << "] ==> pruned(G,pi0,[";
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
    ostr << "PathAxiom: [] ==> on_path(G,pi0,[])" << std::endl;
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
    ostr << "ExtendPath: [on_path(G,pi0,[";
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
    ostr << "] ==> on_path(G,pi0,[";
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

    for(unsigned i = 0; i < _w.size(); i++)
      {
	if(_w[i] == _w_max)
	  continue;

	if(!fd.sequence_exists(convert_to_sequence::pruned(_v, _w[i])))
	  {
	    std::cerr << "PRUNED PREMISE: " << i << " NOT PROVED (MAX: " << _w_max << ")" << std::endl;
	    error_message = "One of 'pruned' premises not proved!";
	    return false;
	  }
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
    ostr << "CanonicalLeaf: [on_path(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    ostr << "]), R(G,pi0,[";
    for(unsigned i = 0; i < _v.size(); i++)
      ostr << _v[i] << " ";
    coloring pi(std::vector<unsigned>(_pi), _g);
    ostr << "]) = " << pi << "] ==> C(G,pi0) = (G^pi,pi0^pi) (for: pi = " << pi << ")" << std::endl;    
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

    fd.add_sequence(convert_to_sequence::canonical());
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

int main(int argc, char ** argv)
{
  if(argc < 3)
    {
      std::cerr << "usage: " << argv[0] << " graph_file proof_file [h]" << std::endl;
      exit(1);
    }
  
  graph g;

  std::ifstream graph_file(argv[1]);

  if(!graph_file)
    {
      std::cerr << "Cannot open file for reading: " << argv[1] << std::endl;
      exit(1);
    }
  
  graph_file >> g;
  graph_file.close();
  std::cout << "Reading graph done" << std::endl;
  coloring pi0(g.num_nodes());

#ifndef _ENABLE_MMAP
  
  std::ifstream istr(argv[2]);

  if(!istr)
    {
      std::cerr << "Cannot open file for reading: " << argv[2] << std::endl;
      exit(1);
    }

#else
  if(!istr.map_file(std::string(argv[2])))
    {
      std::cerr << "Cannot map file for reading: " << argv[2] << std::endl;
      exit(1);
    }

  struct sigaction act;
  sigemptyset(&act.sa_mask);
  act.sa_flags = 0;
  act.sa_handler = handler;  
  sigaction(SIGALRM, &act, NULL);
#endif
  
  rule_ptr rp;

  if(argc >= 4 && argv[3][0] == 'h')
    {      
      while((rp = read_next_rule(istr, g, pi0)).get() != nullptr)
	{     
	  rp->out(std::cout);
	}
      return 0;
    }
  
  fact_database_t fd;
  std::string error_message;

  alarm(1);
  
  while((rp = read_next_rule(istr, g, pi0)).get() != nullptr)
    {      
      if(!rp->check_rule(fd, error_message))
	{	
	  rp->out(std::cout);
	  std::cout << "ERROR: " << error_message << std::endl;
	  return 1;
	}
    }
  
  if(!fd.sequence_exists(convert_to_sequence::canonical()))
    {
      std::cout << "ERROR: Canonical leaf fact not derived!" << std::endl;
      return 1;
    }
  
  std::cout << "OK" << std::endl;
  
  return 0;
}
