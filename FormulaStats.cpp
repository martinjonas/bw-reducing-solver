#include "FormulaStats.h"

#include <algorithm>

void FormulaStats::AddFunctionApplication(const std::string &name, const z3::expr &expr)
{
    auto decl_kind = expr.decl().decl_kind();
    if (decl_kind != Z3_OP_BMUL)
    {
	if (decl_kind != Z3_OP_AND && decl_kind != Z3_OP_OR && decl_kind != Z3_OP_NOT && decl_kind != Z3_OP_IMPLIES)
	{
	    functionSymbols.insert(name);
	}
    }
    else
    {
	if (expr.num_args() == 2 && (expr.arg(0).is_numeral() || expr.arg(0).is_numeral()))
	{
	    functionSymbols.insert("bvmul(scalar)");
	}
	else
	{
	    functionSymbols.insert("bvmul");
	}
    }

    if (expr.is_bv())
    {
	maxBitWidth = std::max(maxBitWidth, expr.get_sort().bv_size());
    }
}

void FormulaStats::AddConstant(const z3::expr &e, const z3::sort &s)
{
    constantASTs.insert(e);

    if (s.is_bool())
    {
	maxBitWidth = std::max(maxBitWidth, 0u);
        constants.insert({e.to_string(), 0});
    }
    else if (s.is_bv())
    {
	maxBitWidth = std::max(maxBitWidth, s.bv_size());
        constants.insert({e.to_string(), s.bv_size()});
    }
}

void FormulaStats::AddVariable(const std::string &name, const z3::sort &s)
{
    variables.insert(name);

    if (s.is_bool())
    {
	maxBitWidth = std::max(maxBitWidth, 0u);
    }
    else if (s.is_bv())
    {
	maxBitWidth = std::max(maxBitWidth, s.bv_size());
    }
}

void FormulaStats::AddNumeral(const std::string &text, const z3::expr &expr)
{
    numerals.insert(text);
}

std::ostream& operator<<(std::ostream& os, const FormulaStats& stats)
{
    std::cout << stats.constants.size() << ",";
    std::cout << stats.variables.size() << ",";
    std::cout << stats.numerals.size() << ",";
    std::cout << stats.maxBitWidth << ",";

    unsigned int i = 0;
    for (const auto& fun : stats.functionSymbols)
    {
	os << fun;
	i++;
	if (i != stats.functionSymbols.size())
	{
	    os << " ";
	}
    }

    return os;
}
