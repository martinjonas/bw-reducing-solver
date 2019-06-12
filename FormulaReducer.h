#pragma once

#include "z3++.h"

class FormulaReducer
{
public:
    z3::expr Reduce(const z3::expr& e, unsigned int newBW, bool keepSign);
};
