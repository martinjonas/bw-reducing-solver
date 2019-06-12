#ifndef FORMULASTATS_H
#define FORMULASTATS_H
#include "z3++.h"
#include <set>
#include <iostream>

class FormulaStats
{
public:
    FormulaStats() {}

    void AddFunctionApplication(const std::string&, const z3::expr&);
    void AddConstant(const z3::expr&, const z3::sort&);
    void AddVariable(const std::string&, const z3::sort&);
    void AddNumeral(const std::string&, const z3::expr&);

    friend std::ostream& operator<<(std::ostream& os, const FormulaStats& stats);

    std::set<std::string> functionSymbols;
    unsigned int maxBitWidth = 0;

    std::set<Z3_ast> constantASTs;
    std::set<std::pair<std::string, int>> constants;
    std::set<std::string> variables;
    std::set<std::string> numerals;

    unsigned int numeralCount = 0;
};

#endif
