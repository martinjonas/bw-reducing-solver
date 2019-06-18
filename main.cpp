#include <iostream>
#include <string>
#include <z3++.h>
#include <cmath>
#include <fstream>
#include <cstdio>
#include <regex>
#include <unistd.h>
#include <climits>
#include <getopt.h>

#include "SMTLIBInterpreter.h"

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

using namespace std;
using namespace z3;
using namespace antlr4;

const std::string boolectorPath = "/tmp/boolector";
std::string verifierPath = "/tmp/boolector";

//TODO: Implementovat!!!
bool substZeroes = false;
bool makeQF = false;
bool dual = false;
bool zeroExtend = false;
bool keepSign = false;

int main(int argc, char* argv[])
{
    static struct option long_options[] = {
        {"dual", no_argument, 0, 'd' },
        {"makeqf", no_argument, 0, 'q' },
        {"zeroextend", no_argument, 0, 'z' },
        {"keepsign", no_argument, 0, 'k' },
        {"verifier", required_argument, 0, 'v' },
	{0,           0,                 0,  0   }
    };

    std::string filename;

    int opt = 0;
    int long_index = 0;
    while ((opt = getopt_long(argc, argv,"dqzkv", long_options, &long_index )) != -1) {
	switch (opt) {
	case 'd':
            dual = true;
	    break;
	case 'q':
            makeQF = true;
	    break;
	case 'z':
            zeroExtend = true;
	    break;
	case 'k':
            keepSign = true;
	    break;
	case 'v':
        {
            string optionString(optarg);
            verifierPath = optionString;
            break;
	}
	default:
	    std::cout << "Invalid arguments" << std::endl << std::endl;
            std::cout << "Usage: formulaReducer filename [--dual, --makeqf, --zeroextend]" << std::endl;
	    return 1;
	}
    }

    if (optind < argc)
    {
	filename = std::string(argv[optind]);
    }
    else
    {
	std::cout << "Filename required" << std::endl;
        std::cout << "Usage: formulaReducer filename [--dual, --makeqf, --zeroextend]" << std::endl;
	return 1;
    }

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.dual = dual;
    interpreter.Run(tree->script());
    exit(0);
}
