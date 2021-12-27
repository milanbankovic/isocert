#ifndef _MEM_MAPPER_H
#define _MEM_MAPPER_H

extern "C" {

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

}

class mem_mapper {
private:
  char * _map = nullptr;
  unsigned long _length = 0;
  unsigned long _curr = 0;
public:

  bool map_file(const std::string & file)
  {
    struct stat s;
    if(stat(file.c_str(), &s) < 0)
      return false;
    _length = s.st_size;
    _curr = 0;
    int fd = 0;
    if((fd = open(file.c_str(), O_RDONLY)) < 0)
      return false;
    _map = (char*)mmap(NULL, _length, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    return _map != MAP_FAILED;
  }
  
  bool read(char * s, unsigned = 0)
  {
    if(_curr == _length)
      return false;

    *s = _map[_curr++];
    return true;    
  }

  unsigned long file_length() const
  {
    return _length;
  }

  unsigned long curr_position() const
  {
    return _curr;
  }
  
};


#endif // _MEM_MAPPER_H
