#include "../sampler/liasampler.h"

struct my_args {
    std::string smtFilePath;
    std::string outputDir{getcwd(NULL, 0)};
    size_t maxNumSamples = 1000;
    double maxTimeLimit = 3600.0;
    sampler::SamplingMode mode = sampler::HYBRID;
    int randomSeed = 0;
    size_t cdclEpoch = 1;
    double fixedVarsPct = 0.5;
};

void printHelp(const char* programName) {
    std::cout << "Usage: " << programName << " [options]\n";
    std::cout << "Options:\n";
    std::cout << "  -i <smt file>               Specify the path to the input file\n";
    std::cout << "  -o <output dir>             Specify the output directory path\n";
    std::cout << "  -n <num samples>            Specify the number of samples\n";
    std::cout << "  -t <time limit>             Set the time limit (in seconds)\n";
    std::cout << "  -s <seed>                   Set the random seed\n";
    std::cout << "  -m <sampling mode>          Set the sampling mode <ls, cdcl, hybrid>\n";
    std::cout << "  -e <cdcl epoch>             Set CDCL epochs for sampling (Only effective in hybrid mode)\n";
    std::cout << "  -p <fixed var percentage>   Set the percentage of fixed variables (Only effective in hybrid mode)\n";
    std::cout << "  -h                          Display this help message\n";
}

bool parseOpt(my_args* argp, int argc, char* argv[]) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "-h") {
            printHelp(argv[0]);
            return false;
        } else if (arg == "-i") {
            if (i + 1 < argc)
                argp->smtFilePath = argv[++i];
            else {
                std::cerr << "Please enter a smt file." << std::endl;
                return false;
            }
        } else if (arg == "-o") {
            if (i + 1 < argc)
                argp->outputDir = argv[++i];
            else {
                std::cerr << "Please enter an output directory." << std::endl;
                return false;
            }
        } else if (arg == "-n") {
            if (i + 1 < argc)
                argp->maxNumSamples = atoll(argv[++i]);
            else {
                std::cerr << "Please specify the number of samples." << std::endl;
                return false;
            }
        } else if (arg == "-t") {
            if (i + 1 < argc)
                argp->maxTimeLimit = atof(argv[++i]);
            else {
                std::cerr << "Please specify a time limit." << std::endl;
                return false;
            }
        } else if (arg == "-s") {
            if (i + 1 < argc)
                argp->randomSeed = atoi(argv[++i]);
            else {
                std::cerr << "Please enter a seed value." << std::endl;
                return false;
            }
        } else if (arg == "-m") {
            if (i + 1 < argc) {
                ++i;
                std::string m = argv[i];
                if (m == "ls" || m == "LS") {
                    argp->mode = sampler::LS;
                } else if (m == "cdcl" || m == "CDCL") {
                    argp->mode = sampler::CDCL;
                } else if (m == "hybrid" || m == "HYBRID") {
                    argp->mode = sampler::HYBRID;
                } else if (m == "2ls" || m == "2LS"){
                    argp->mode = sampler::LS_ITER;
                } else{
                    std::cerr << "Unknown sampling mode " << m << std::endl;
                    return false;
                }
            } else {
                std::cerr << "Please select sampling mode." << std::endl;
                return false;
            }

        } else if (arg == "-e") {
            if (i + 1 < argc)
                argp->randomSeed = atoll(argv[++i]);
            else {
                std::cerr << "Please enter CDCL epochs." << std::endl;
                return false;
            }
        } else if (arg == "-p") {
            if (i + 1 < argc)
                argp->randomSeed = atof(argv[++i]);
            else {
                std::cerr << "Please enter fixed vars percentage." << std::endl;
                return false;
            }
        } else {
            std::cerr << "Unknown argument: " << arg << std::endl;
            return false;
        }
    }
    return true;
}

int main(int argc, char* argv[]) {
    // Z3_enable_trace("solve_eqs_round");
    // Z3_enable_trace("solve_eqs_subst");
    // Z3_enable_trace("solve_eqs");
    Z3_enable_trace("sampling_init");
    Z3_enable_trace("sampler");

    if (argc == 1) {
        printHelp(argv[0]);
        return 1;
    }

    my_args arg;
    bool parseRes = parseOpt(&arg, argc, argv);
    if (!parseRes) {
        return 1;
    }

    z3::context ctx;
    sampler::LiaSampler mySampler(&ctx , arg.smtFilePath, arg.outputDir, arg.maxNumSamples, arg.maxTimeLimit, arg.mode, arg.randomSeed, arg.cdclEpoch, arg.fixedVarsPct);

    mySampler.sampling();

    return 0;
}