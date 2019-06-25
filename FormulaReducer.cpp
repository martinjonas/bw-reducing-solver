#include "FormulaReducer.h"

z3::expr FormulaReducer::Reduce(const z3::expr &e, unsigned int newBW, bool keepSign)
{
    if (e.is_numeral())
    {
        if (e.is_bv() && e.get_sort().bv_size() <= newBW)
        {
            return e;
        }

        if (e.is_bv() && e.get_sort().bv_size() > newBW)
        {
            if (keepSign && newBW > 2)
            {
                auto bw = e.get_sort().bv_size();
                return z3::concat(e.extract(bw - 1, bw - 1), e.extract(newBW-2, 0)).simplify();
            }

            return e.extract(newBW-1, 0).simplify();
        }

        return e;
    }
    else if (e.is_const())
    {
        if (e.is_bv() && e.get_sort().bv_size() <= newBW)
        {
            return e;
        }

        if (e.is_bv() && e.get_sort().bv_size() > newBW)
        {
            z3::expr newVar = e.ctx().bv_const(e.to_string().c_str(), newBW);
            return newVar;
        }

        return e;
    }
    else if (e.is_var())
    {
        if (e.is_bv() && e.get_sort().bv_size() <= newBW)
        {
            return e;
        }

        if (e.is_bv() && e.get_sort().bv_size() > newBW)
        {
            z3::expr newVar(e.ctx(), Z3_mk_bound(e.ctx(), Z3_get_index_value(e.ctx(), e), Z3_mk_bv_sort(e.ctx(), newBW)));
            return newVar;
        }

        return e;
    }
    else if (e.is_app())
    {
	z3::func_decl f = e.decl();
	unsigned num = e.num_args();

        z3::expr_vector arguments(e.ctx());
	for (unsigned int i = 0; i < num; i++)
	{
            arguments.push_back(Reduce(e.arg(i), newBW, keepSign));
	}

        unsigned int argBits;
        switch (f.decl_kind())
        {
        case Z3_OP_ZERO_EXT:
            argBits = e.arg(0).get_sort().bv_size();
            if (argBits >= newBW)
            {
                return arguments[0];
            }
            else
            {
                return z3::expr(e.ctx(), Z3_mk_zero_ext(e.ctx(), newBW - argBits, e.arg(0)));
            }
        case Z3_OP_SIGN_EXT:
            argBits = e.arg(0).get_sort().bv_size();
            if (argBits >= newBW)
            {
                return arguments[0];
            }
            else
            {
                return z3::expr(e.ctx(), Z3_mk_sign_ext(e.ctx(), newBW - argBits, e.arg(0)));
            }
        case Z3_OP_AND:
        case Z3_OP_OR:
        case Z3_OP_XOR:
        case Z3_OP_IMPLIES:
        case Z3_OP_IFF:
            return f(arguments);
        case Z3_OP_ITE:
            return z3::ite(arguments[0], arguments[1], arguments[2]);
        case Z3_OP_BNEG:
            return -arguments[0];
        case Z3_OP_BSUB:
            return arguments[0] - arguments[1];
        case Z3_OP_BAND:
            return arguments[0] & arguments[1];
        case Z3_OP_BOR:
            return arguments[0] | arguments[1];
        case Z3_OP_BXOR:
            return arguments[0] ^ arguments[1];
        case Z3_OP_BNAND:
            return z3::nand(arguments[0], arguments[1]);
        case Z3_OP_BNOR:
            return z3::nor(arguments[0], arguments[1]);
        case Z3_OP_BXNOR:
            return z3::xnor(arguments[0], arguments[1]);
        case Z3_OP_BNOT:
            return ~arguments[0];
        case Z3_OP_BMUL:
        {
            auto result = arguments[0];
            for (unsigned int i = 1; i < num; i++)
            {
                result = result * arguments[i];
            }
            return result;
        }
        case Z3_OP_BADD:
        {
            auto result = arguments[0];
            for (unsigned int i = 1; i < num; i++)
            {
                result = result + arguments[i];
            }
            return result;
        }
        case Z3_OP_BSDIV:
        case Z3_OP_BSDIV_I:
            return arguments[0] / arguments[1];
        case Z3_OP_BUDIV:
        case Z3_OP_BUDIV_I:
            return z3::expr(e.ctx(), Z3_mk_bvudiv(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_BUREM:
        case Z3_OP_BUREM_I:
            return z3::expr(e.ctx(), Z3_mk_bvurem(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_BSREM:
        case Z3_OP_BSREM_I:
            return z3::expr(e.ctx(), Z3_mk_bvsrem(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_BSHL:
            return z3::expr(e.ctx(), Z3_mk_bvshl(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_BASHR:
            return z3::expr(e.ctx(), Z3_mk_bvashr(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_BLSHR:
            return z3::expr(e.ctx(), Z3_mk_bvlshr(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_SLT:
            return arguments[0] < arguments[1];
        case Z3_OP_SLEQ:
            return arguments[0] <= arguments[1];
        case Z3_OP_SGT:
            return arguments[0] > arguments[1];
        case Z3_OP_SGEQ:
            return arguments[0] >= arguments[1];
        case Z3_OP_ULT:
            return z3::expr(e.ctx(), Z3_mk_bvult(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_ULEQ:
            return z3::expr(e.ctx(), Z3_mk_bvule(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_UGT:
            return z3::expr(e.ctx(), Z3_mk_bvugt(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_UGEQ:
            return z3::expr(e.ctx(), Z3_mk_bvuge(e.ctx(), arguments[0], arguments[1]));
        case Z3_OP_EQ:
            return arguments[0] == arguments[1];
        case Z3_OP_DISTINCT:
            return z3::distinct(arguments);
        case Z3_OP_NOT:
            return !arguments[0];
        case Z3_OP_CONCAT:
            if (num > 2)
            {
                std::cout << "Unsupported concat of artity > 2" << std::endl;
                std::cout << "unknown" << std::endl;
                exit(1);
            }

            if ((arguments[0].get_sort().bv_size() + arguments[1].get_sort().bv_size() ) <= newBW)
            {
                return z3::concat(arguments[0], arguments[1]);
            }

            if (e.arg(1).get_sort().bv_size() >= newBW)
            {
                return arguments[1];
            }
            else
            {
                return z3::concat(arguments[0].extract(newBW - e.arg(1).get_sort().bv_size() - 1, 0),
                                  arguments[1]);
            }
        case Z3_OP_EXTRACT:
	    Z3_func_decl z3decl = (Z3_func_decl)e.decl();

	    int hi = Z3_get_decl_int_parameter(e.ctx(), z3decl, 0);
	    int lo = Z3_get_decl_int_parameter(e.ctx(), z3decl, 1);

            if (newBW > hi)
            {
                return arguments[0].extract(hi, lo);
            }
            else if (newBW <= lo)
            {
                return e.ctx().bv_val(0, newBW);
            }
            else
            {
                return z3::zext(arguments[0].extract(arguments[0].get_sort().bv_size(), lo),
                                lo);
            }
        }

        std::cout << e << std::endl;
        exit(1);
    }
    else if (e.is_quantifier())
    {
        auto& context = e.ctx();
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(context, ast);
	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];

	for (int i = 0; i < numBound; i++)
	{
            z3::sort s(e.ctx(), Z3_get_quantifier_bound_sort(context, ast, i));
            if (s.is_bv() && s.bv_size() > newBW)
            {
                sorts[i] = e.ctx().bv_sort(newBW);
            }
            else
            {
                sorts[i] = s;
            }
	    decl_names[i] = Z3_get_quantifier_bound_name(context, ast, i);
	}

	Z3_ast quantAst = Z3_mk_quantifier(
	    context,
	    Z3_is_quantifier_forall(context, ast),
	    Z3_get_quantifier_weight(context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)Reduce(e.body(), newBW, keepSign));
	return to_expr(context, quantAst);
    }

    return e;
}
