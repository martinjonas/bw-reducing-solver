#include "ExprSimplifier.h"
#include <string>
#include <sstream>
#include <numeric>

using namespace z3;

#define DEBUG false

expr ExprSimplifier::PushNegations(const expr &e)
{
    auto item = pushNegationsCache.find((Z3_ast)e);
    if (false && item != pushNegationsCache.end())
    {
        return item->second;
    }

    if (e.is_app())
    {
        if (e.decl().decl_kind() == Z3_OP_IMPLIES)
        {
            return PushNegations(!e.arg(0)) || PushNegations(e.arg(1));
        }
        if (e.decl().decl_kind() != Z3_OP_NOT)
        {
            func_decl dec = e.decl();
            int numArgs = e.num_args();

            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                if (e.arg(i).is_bool())
                {
                    arguments.push_back(PushNegations(e.arg(i)));
                }
                else
                {
                    arguments.push_back(e.arg(i));
                }
            }

            auto result = dec(arguments);
            pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
        else
        {
            expr notBody = e.arg(0);
            if (notBody.is_app())
            {
                func_decl innerDecl = notBody.decl();
                int numArgs = notBody.num_args();

                if (innerDecl.decl_kind() == Z3_OP_NOT)
                {
                    auto result = PushNegations(notBody.arg(0));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_AND)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_or(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_OR)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_and(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_ITE)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(!notBody.arg(2)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_IFF)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(notBody.arg(1)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
		else if (innerDecl.decl_kind() == Z3_OP_SLEQ)
		{
		    return notBody.arg(1) < notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_SLT)
		{
		    return notBody.arg(1) <= notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULEQ)
		{
		    return to_expr(*context, Z3_mk_bvult(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULT)
		{
		    return to_expr(*context, Z3_mk_bvule(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
            }
            else if (notBody.is_quantifier())
            {

                auto result = flipQuantifierAndModifyBody(notBody, PushNegations(!notBody.body()));
                //pushNegationsCache.insert({(Z3_ast)e, result});
                return result;
            }

            auto result = e;
            //pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
    }
    if (e.is_quantifier())
    {
	expr result = modifyQuantifierBody(e, PushNegations(e.body()));
        pushNegationsCache.insert({(Z3_ast)e, result});
        return result;
    }

    auto result = e;
    pushNegationsCache.insert({(Z3_ast)e, result});
    return result;
}

expr ExprSimplifier::CanonizeBoundVariables(const expr &e)
{
    if (e.is_app() && e.get_sort().is_bool())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(CanonizeBoundVariables(e.arg(i)));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
        {
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	    decl_names[i] = Z3_mk_string_symbol(*context, ("canon_x" + std::to_string(lastBound)).c_str());

	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);
	    canonizeVariableRenaming.insert({"canon_x" + std::to_string(lastBound), current_symbol.str()});

	    lastBound++;
        }

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)CanonizeBoundVariables(e.body() && context->bool_val(true)).arg(0));

	auto result = to_expr(*context, quantAst);
	return result;
    }
    else
    {
	return e;
    }
}

expr ExprSimplifier::DeCanonizeBoundVariables(const expr &e)
{
    if (e.is_app() && e.get_sort().is_bool())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(DeCanonizeBoundVariables(e.arg(i)));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
        {
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);

	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    decl_names[i] = Z3_mk_string_symbol(*context, (canonizeVariableRenaming[current_symbol.str()]).c_str());
        }

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)DeCanonizeBoundVariables(e.body() && context->bool_val(true)));

	auto result = to_expr(*context, quantAst);
	return result;
    }
    else
    {
	return e;
    }
}

expr ExprSimplifier::mk_or(const expr_vector &args) const
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_or(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::mk_and(const expr_vector &args) const
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_and(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::modifyQuantifierBody(const expr& quantifierExpr, const expr& newBody) const
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

expr ExprSimplifier::flipQuantifierAndModifyBody(const expr& quantifierExpr, const expr& newBody) const
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	!Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

void ExprSimplifier::clearCaches()
{
    pushIrrelevantCache.clear();
    refinedPushIrrelevantCache.clear();
    decreaseDeBruijnCache.clear();
    isRelevantCache.clear();
    reduceDivRemCache.clear();
}

bool ExprSimplifier::isVar(const expr& e) const
{
    if (e.is_var())
    {
        return true;
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL && !e.is_numeral())
	{
	    return true;
	}
    }

    return false;
}

z3::expr ExprSimplifier::StripToplevelExistentials(z3::expr e, bool isPositive)
{
    // only for quantifiers on the very top level to keep the overhead minimal
    if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
	if ((isPositive && !Z3_is_quantifier_forall(*context, ast)) ||
            (!isPositive && Z3_is_quantifier_forall(*context, ast)))
	{
	    int numBound = Z3_get_quantifier_num_bound(*context, ast);

	    z3::expr_vector currentBound(*context);
	    for (int i = numBound - 1; i >= 0; i--)
	    {
		z3::sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
		Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
		z3::symbol current_symbol(*context, z3_symbol);

		auto name = current_symbol.str();
		if (s.is_bool())
		{
		    currentBound.push_back(context->bool_const(name.c_str()));
		}
		else if (s.is_bv())
		{
		    currentBound.push_back(context->bv_const(name.c_str(), s.bv_size()));
		}
		else
		{
		    std::cout << "Unsupported quantifier sort" << std::endl;
		    std::cout << "unknown" << std::endl;
		    abort();
		}
	    }

	    auto body = e.body().substitute(currentBound);
	    return StripToplevelExistentials(body, isPositive);
	}
    }
    else if (e.is_app())
    {
        func_decl decl = e.decl();
        int numArgs = e.num_args();

        if (decl.decl_kind() == Z3_OP_OR)
        {
            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                arguments.push_back(StripToplevelExistentials(e.arg(i), isPositive));
            }

            auto result = mk_or(arguments);
            return result;
        }
        else if (decl.decl_kind() == Z3_OP_AND)
        {
            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                arguments.push_back(StripToplevelExistentials(e.arg(i), isPositive));
            }

            auto result = mk_and(arguments);
            return result;
        }
        else if (decl.decl_kind() == Z3_OP_NOT)
        {
            return !StripToplevelExistentials(e.arg(0), !isPositive);
        }
        else if (decl.decl_kind() == Z3_OP_IMPLIES)
        {
            return z3::implies(StripToplevelExistentials(e.arg(0), !isPositive),
                               StripToplevelExistentials(e.arg(0), isPositive));
        }
    }

    return e;
}

z3::expr ExprSimplifier::RemoveExistentials(z3::expr e)
{
   if (e.is_app() && e.get_sort().is_bool())
   {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(RemoveExistentials(e.arg(i)));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
        z3::expr_vector currentBound(*context);

	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	for (int i = 0; i < numBound; i++)
        {
	    Z3_sort z3_sort = Z3_get_quantifier_bound_sort(e.ctx(), ast, i);
            z3::sort current_sort(e.ctx(), z3_sort);

            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            z3::symbol current_symbol(*context, z3_symbol);
            auto name = current_symbol.str();

            if (Z3_is_quantifier_forall(*context, ast))
            {
                if (current_sort.is_bool())
		{
		    currentBound.push_back(context->bool_const(name.c_str()));
		}
		else if (current_sort.is_bv())
		{
		    currentBound.push_back(context->bv_const(name.c_str(), current_sort.bv_size()));
		}
            }
            else
            {
                if (current_sort.is_bool())
                {
                    currentBound.push_back(context->bool_val(0));
                }
                else if (current_sort.is_bv())
                {
                    currentBound.push_back(context->bv_val(0, current_sort.bv_size()));
                }
            }
        }

        auto body = e.body().substitute(currentBound);
        return RemoveExistentials(body);
    }
    else
    {
	return e;
    }
}

z3::expr ExprSimplifier::SubstituteExistentials(z3::expr e, std::map<std::string, z3::expr>& model, std::vector<std::string>& boundVars)
{
    if (e.is_numeral())
    {
        return e;
    }

    if (e.is_const())
    {
        std::string name = e.to_string();

        if (model.find(name) != model.end())
        {
            z3::expr value =  model.at(name);
            return to_expr(e.ctx(), Z3_translate(value.ctx(), value, e.ctx()));
        }

        return e;
    }
    else if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        std::string name = boundVars[boundVars.size() - deBruijnIndex - 1];

        if (model.find(name) != model.end())
        {
            z3::expr value = model.at(name);
            return to_expr(e.ctx(), Z3_translate(value.ctx(), value, e.ctx()));
        }

        return e.is_bool() ? e.ctx().bool_const(name.c_str()) : e.ctx().bv_const(name.c_str(), e.get_sort().bv_size());

        return e;
    }
    else if (e.is_app())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(SubstituteExistentials(e.arg(i), model, boundVars));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;
	int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

	for (int i = 0; i < boundVariables; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    boundVars.push_back(current_symbol.str());
	}

        auto newBody = SubstituteExistentials(e.body(), model, boundVars);
        e = modifyQuantifierBody(e, newBody);

        boundVars.erase(boundVars.end() - boundVariables, boundVars.end());
        return e;
    }

    std::cout << "Unsupported " << e << std::endl;
    exit(1);
}

bool ExprSimplifier::isSentence(const z3::expr &e)
{
    auto item = isSentenceCache.find((Z3_ast)e);
    if (item != isSentenceCache.end())
    {
	return item->second;
    }

    if (e.is_var())
    {
	return true;
    }
    else if (e.is_const() && !e.is_numeral())
    {
	std::stringstream ss;
	ss << e;
	if (ss.str() == "true" || ss.str() == "false")
	{
	    return true;
	}

	return false;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	for (unsigned int i = 0; i < num; i++)
	{
	    if (!isSentence(e.arg(i)))
	    {
		isSentenceCache.insert({(Z3_ast)e, false});
		return false;
	    }
	}

	isSentenceCache.insert({(Z3_ast)e, true});
	return true;
    }
    else if(e.is_quantifier())
    {
	return isSentence(e.body());
    }

    return true;
}
