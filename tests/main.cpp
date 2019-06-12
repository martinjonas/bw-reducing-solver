#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch.hpp"

#include "../SMTLIBInterpreter.h"

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

using namespace antlr4;

std::map<std::string, std::vector<bool>> model;

Result Solve(std::string filename)
{
    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    return interpreter.Run(tree->script());
}

TEST_CASE( "Simple SAT", "[simple-sat]" )
{
    REQUIRE( Solve("../tests/data/plusInverse_sat.smt2") == SAT );
}
