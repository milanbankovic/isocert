#ifndef UTILITY_H
#define UTILITY_H

#include <cstdlib>
#include <string>

namespace morphi {

template<typename FunctionType>
struct OnReturn {
    FunctionType m_f;
    OnReturn(FunctionType f) : m_f(f) {}
    ~OnReturn() { m_f(); }
};

enum ProofType {
    None,
    SearchTree,
    PrunedTree
};

struct Options {
    bool relabel = false;
    ProofType proof_type = ProofType::None;
    std::string proof_file = "proof.out";
    size_t aut_limit = 500;
};

struct ArgumentParser {

    ArgumentParser(size_t argc, char* argv[]) {
        parsed = true;
        size_t idx = 1;
        while(idx < argc) {
            std::string arg(argv[idx++]);
            if(arg.find("--aut-limit=") == 0)
                options.aut_limit = std::stoul(arg.substr(arg.find("=") + 1));
            else if(arg == "-a") {
                if(idx == argc) {
                    parsed = false;
                    break;
                }
                options.aut_limit = std::stoul(argv[idx++]);
            }
            else if(arg.find("--mem-limit=") == 0)
                mem_limit = std::stoull(arg.substr(arg.find("=") + 1)) * (1ull << 20);
            else if(arg == "-m") {
                if(idx == argc) {
                    parsed = false;
                    break;
                }
                mem_limit = std::stoull(argv[idx++]) * (1ull << 20);
            }
            else if(arg == "-o") {
                if(idx == argc) {
                    parsed = false;
                    break;
                }
                options.proof_file = std::string(argv[idx++]);
            }
            else if(arg == "-p")
                options.proof_type = ProofType::PrunedTree;
            else if(arg == "-d")
                options.proof_type = ProofType::SearchTree;
            else {
                parsed = false;
                break;
            }
        }
    }

    // Parsed correctly? flag
    bool parsed;

    // Options
    uint64_t mem_limit = 1ull << 30;
    Options options;
};

} // namespace

#endif // UTILITY_H
