#ifndef _HASH_DATABASE_H
#define _HASH_DATABASE_H

#include <unordered_set>

template <typename T>
class hash_database {
public:
  using elem_type = T;
private:

  class vector_hash {
  public:
    unsigned long operator () (const std::vector<T> & v) const
    {
      unsigned long ret = 0;
      for(const T & x : v)
	ret = ret * 157 + (unsigned long)x;
      return ret;
    }
  };
    
  std::unordered_set<std::vector<T>, vector_hash> _database;
  
public:  
  
  void add_sequence(const std::vector<elem_type> & seq)
  {
    add_sequence(std::vector<elem_type>(seq));
  }
  
  void add_sequence(std::vector<elem_type> && seq)
  {
    _database.insert(std::move(seq));
  }

  bool sequence_exists(const std::vector<elem_type> & seq) const
  {
    return _database.find(seq) != _database.end();
  }

};


#endif // _HASH_DATABASE_H
