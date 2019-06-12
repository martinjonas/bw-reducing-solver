#include "Solver.h"
#include "FormulaTraverser.h"
#include "FormulaStats.h"
#include "FormulaReducer.h"
#include "ExprSimplifier.h"

#include<unistd.h>
#include<sys/wait.h>
#include<sys/prctl.h>
#include<signal.h>
#include<stdlib.h>
#include<string.h>
#include<stdio.h>

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
    std::cout << reducedFormula;

    //TODO: Run Boolector
    return UNKNOWN;
}
