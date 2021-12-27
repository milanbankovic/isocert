#include <iostream>
#include <fstream>
#include <sstream>

#include "algorithm_selector.h"
#include "utility.h"

int main(int argc, char* argv[])
{
    morphi::ArgumentParser args(argc, argv);
    if(!args.parsed) {
        std::cerr << "Usage: " << argv[0] << " [OPTIONS]... < GraphFile > CanonFile" << std::endl;
        std::cerr << "Generate a canonical form of the input graph. GraphFile must be DIMACS formatted." << std::endl;
        std::cerr << std::endl;
        std::cerr << "  -a <num>  --aut-limit=<num>    Limit number of stored automorphisms (default=500)" << std::endl;
        std::cerr << "  -m <num>  --mem-limit=<num>    Limit virtual memory in MB (default=2048)" << std::endl;
        std::cerr << "  -o <file>                      Set proof file (default=proof.out)" << std::endl;
        std::cerr << "  -d                             Generate proof (during search)" << std::endl;
        std::cerr << "  -p                             Generate proof (post-search)" << std::endl;
        return -1;
    }

    morphi::global_alloc.reserve(args.mem_limit);
    srand(time(0));

    morphi::AlgorithmSelector selector(std::cin, args.options);
    selector.run();

    return 0;
}
