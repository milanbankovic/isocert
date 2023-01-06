#ifndef _TRIE_H
#define _TRIE_H

#include <memory>
#include <optional>
#include <unordered_map>
#include <algorithm>
#include <iterator>

template <typename T>
class trie {
public:
  using elem_type = T;
private:

  class trie_node;
  
  using trie_node_ptr = std::shared_ptr<trie_node>;

  struct trie_node {
    std::vector<elem_type> _elems;
    std::optional<std::unordered_map<elem_type, trie_node_ptr>> _children;
    bool _valid;
    
    trie_node(std::vector<elem_type> && seq)
      :_elems(std::move(seq)),
       _valid(true)
    {}

    trie_node()
      :_valid(false)
    {}
  };



  trie_node_ptr _root = nullptr;

  static unsigned find_common_prefix_length(const std::vector<elem_type> & seq, unsigned start,
					    const std::vector<elem_type> & elems)
  {
    for(unsigned i = 0; start + i < seq.size() && i < elems.size(); i++)
      if(seq[start + i] != elems[i])
	return i;

    return std::min(seq.size() - start, elems.size());
  }
  
public:
  void add_sequence(const std::vector<elem_type> & seq)
  {
    add_sequence(std::vector<elem_type>(seq));
  }
  
  void add_sequence(std::vector<elem_type> && seq)
  {
    if(_root.get() == nullptr)
      {
	_root = std::make_shared<trie_node>(std::move(seq));	
      }
    else
      {
	trie_node_ptr curr_node = _root;
	trie_node_ptr prev_node = nullptr;
	unsigned start = 0;

	while(true)
	  {
	    unsigned k = find_common_prefix_length(seq, start, curr_node->_elems);
	    if(k < curr_node->_elems.size())
	      {
		// split needed	    
		trie_node_ptr new_node = std::make_shared<trie_node>();
		std::swap(curr_node->_elems, new_node->_elems);
		std::copy(std::make_move_iterator(new_node->_elems.begin() + k),
			  std::make_move_iterator(new_node->_elems.end()),
			  std::back_inserter(curr_node->_elems));		
		new_node->_elems.resize(k);
		new_node->_children = std::unordered_map<elem_type, trie_node_ptr>();
		new_node->_children->insert({curr_node->_elems[0], curr_node});
		if(start + k < seq.size())
		  {
		    trie_node_ptr add_node = std::make_shared<trie_node>();
		    std::copy(std::make_move_iterator(seq.begin() + start + k),
			      std::make_move_iterator( seq.end()), std::back_inserter(add_node->_elems));
		    new_node->_children->insert({add_node->_elems[0], add_node});
		    add_node->_valid = true;
		  }
		else
		  {
		    new_node->_valid = true;
		  }
		
		if(curr_node == _root)
		  _root = new_node;
		else
		  {
		    (*prev_node->_children)[new_node->_elems[0]] = new_node;
		  }		  
		break;
	      }
	    else if(start + k < seq.size())
	      {
		if(!curr_node->_children.has_value())
		  {
		    curr_node->_children = std::unordered_map<elem_type, trie_node_ptr>();		
		  }

		auto it = curr_node->_children->find(seq[start + k]);
		if(it != curr_node->_children->end())
		  {
		    start += k;
		    prev_node = curr_node;
		    curr_node = it->second;
		    continue;
		  }
		else
		  {
		    trie_node_ptr new_node = std::make_shared<trie_node>();
		    std::copy(std::make_move_iterator(seq.begin() + start + k),
			      std::make_move_iterator(seq.end()),
			      std::back_inserter(new_node->_elems));
		    new_node->_valid = true;
		    curr_node->_children->insert({new_node->_elems[0], new_node});
		    break;
		  }
	      }
	    else
	      {
		curr_node->_valid = true;
		break;
	      }
	  }
      }
  }

  bool sequence_exists(const std::vector<elem_type> & seq) const
  {
    if(_root.get() == nullptr)
      return false;

    trie_node_ptr curr_node = _root;
    unsigned start = 0;
    
    while(true)
      {
	unsigned k = find_common_prefix_length(seq, start, curr_node->_elems);
	if(k < curr_node->_elems.size())
	  return false;
	else if(start + k == seq.size())
	  return curr_node->_valid;
	else
	  {
	    if(!curr_node->_children.has_value())
	      return false;
	    
	    auto it = curr_node->_children->find(seq[start + k]);
	    if(it != curr_node->_children->end())
	      {
		start += k;
		curr_node = it->second;
	      }
	    else
	      return false;
	  }		
      }
    return false;
  }
};

#endif // _TRIE_H
