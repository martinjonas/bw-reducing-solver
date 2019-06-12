#ifndef FORMULATRAVERSER_H
#define FORMULATRAVERSER_H
#include "z3++.h"
#include "FormulaStats.h"
#include <set>

template <class T>
class FormulaTraverser
{
public:
    FormulaTraverser() {}

    void Traverse(const z3::expr&);

    T GetData()
    {
	return data;
    }

private:
    T data;

    std::set<Z3_ast> processedCache;
};

template<class T>
void FormulaTraverser<T>::Traverse(const z3::expr &expr)
{
    auto item = processedCache.find((Z3_ast)expr);
    if (item != processedCache.end())
    {
	return;
    }

    if (expr.is_numeral())
    {
	std::stringstream ss;
	ss << expr;

	data.AddNumeral(ss.str(), expr);
    }
    else if (expr.is_const())
    {
	std::stringstream ss;
	ss << expr;

	if (ss.str() == "true" || ss.str() == "false")
	{
	    return;
	}

	data.AddConstant(expr, expr.get_sort());
    }
    else if (expr.is_app())
    {
	z3::func_decl f = expr.decl();
	unsigned num = expr.num_args();

	if (num != 0)
	{
	    data.AddFunctionApplication(f.name().str(), expr);
	}

	for (unsigned i = 0; i < num; i++)
	{
	    Traverse(expr.arg(i));
	}
    }
    else if (expr.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)expr;

        int boundVariables = Z3_get_quantifier_num_bound(expr.ctx(), ast);

        for (int i = 0; i < boundVariables; i++)
        {
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(expr.ctx(), ast, i);
	    Z3_sort z3_sort = Z3_get_quantifier_bound_sort(expr.ctx(), ast, i);

	    z3::symbol current_symbol(expr.ctx(), z3_symbol);
            z3::sort current_sort(expr.ctx(), z3_sort);

	    data.AddVariable(current_symbol.str(), current_sort);
        }

        Traverse(expr.body());
    }

    processedCache.insert((Z3_ast)expr);
}


#endif
