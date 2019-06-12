#include "Solver.h"
#include "FormulaTraverser.h"
#include "FormulaStats.h"
#include "FormulaReducer.h"
#include "ExprSimplifier.h"

#include <cstdio>
#include <regex>
#include "boost/process.hpp"

Result Solver::Solve(const z3::expr &formula)
{
    FormulaTraverser<FormulaStats> traverser;
    traverser.Traverse(formula);

    FormulaStats formulaStats = traverser.GetData();
    if (formulaStats.functionSymbols.find("concat") != formulaStats.functionSymbols.end() ||
        formulaStats.functionSymbols.find("extract") != formulaStats.functionSymbols.end())
    {
        std::cout << "unsupported concat/extract" << std::endl;
        std::cout << "unknown" << std::endl;
        exit(1);
    }

    ExprSimplifier simplifier(formula.ctx());
    z3::expr canonized = simplifier.CanonizeBoundVariables(formula);
    canonized = simplifier.PushNegations(canonized);
    canonized = simplifier.StripToplevelExistentials(canonized, true);

    for (unsigned int i = 1; i <= formulaStats.maxBitWidth; i *= 2)
    {
        std::cout << "---" << std::endl;
        std::cout << "Solving the formula reduced to " << i << " bits" << std::endl;
        Result result = solveReduced(canonized, i);

        if (result == SAT)
        {
            return SAT;
        }
    }

    std::cout << "unknown" << std::endl;
    return UNKNOWN;
}

Result Solver::SolveDual(const z3::expr &formula)
{

}

Result Solver::solveReduced(const z3::expr &formula, int bw)
{
    FormulaReducer reducer;
    z3::expr reducedFormula = reducer.Reduce(formula, bw, true);
    std::cout << reducedFormula << std::endl;

    boost::process::opstream in;
    boost::process::ipstream out;
    boost::process::child c(boost::process::search_path("boolector"), "--quant:dual=0", boost::process::std_out > out, boost::process::std_in < in);

    in << "(set-logic BV)" << std::endl;
    in << "(set-option :produce-models true)" << std::endl;
    in << "(assert " << reducedFormula << ")" << std::endl;
    in << "(check-sat)" << std::endl;
    in << "(get-model)" << std::endl;
    in << "(exit)" << std::endl;

    std::string line;
    std::getline(out, line);

    if (line == "sat")
    {
        std::cout << "The reduced formula is SAT" << std::endl;

        getline(out, line);
        //the solver has returned an assignment to some variables; use it
        if (line == "(model")
        {
            std::cout << "The model is available:" << std::endl;

            std::regex varRegex ("(\\w+)!(\\d|!)+(\\s|\\)|$)");
            while (c.running() && getline(out, line) && line != ")")
            {
                std::cout << line << std::endl;
            }
        }
    }

    c.wait();

    return UNKNOWN;
}
