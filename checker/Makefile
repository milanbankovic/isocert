.PHONY: clean

CXXFLAGS = -Wall -O3 -std=c++17 -DNDEBUG
ADDFLAGS = 

checker: common.hpp trie.hpp hash_database.hpp checker.cpp
	g++ $(CXXFLAGS) -D_ENABLE_MMAP -D_PREFIX_TREE $(ADDFLAGS) -o checker checker.cpp

clean:
	rm -f checker
	rm -f *~
	rm -f *.o
