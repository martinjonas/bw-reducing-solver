#pragma once

#include <z3++.h>
#include "FormulaStats.h"

#include <map>
#include <functional>

enum Result { SAT, UNSAT, UNKNOWN, NORESULT };

class SMTLIBInterpreter;

class Solver
{
public:
    Result Solve(const z3::expr& formula);
    Result SolveDual(const z3::expr& formula);

private:
    Result solveReduced(const z3::expr& formula, int bw);
    std::map<z3::expr, z3::expr> getExtendedModel(const SMTLIBInterpreter&);

    FormulaStats originalFormulaStats;
    SMTLIBInterpreter* modelInterpreter;

    z3::expr extendTerm(const z3::expr& e);
    z3::expr changeBW(const z3::expr& e, int bw);

    bool verify(const z3::expr& formula, std::string verifyingSolver);
};
