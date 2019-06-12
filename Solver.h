#pragma once

#include <z3++.h>

enum Result { SAT, UNSAT, UNKNOWN, NORESULT };

class Solver
{
public:
    Result Solve(const z3::expr& formula);
    Result SolveDual(const z3::expr& formula);

private:
    Result solveReduced(const z3::expr& formula, int bw);
};
