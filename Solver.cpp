#include "Solver.h"
#include "FormulaTraverser.h"
#include "FormulaReducer.h"
#include "ExprSimplifier.h"
#include "SMTLIBInterpreter.h"


#include "SMTLIBv2BaseVisitor.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"
#include "antlr4-runtime.h"

#include <cstdio>
#include <regex>
#include "boost/process.hpp"

using namespace antlr4;

Result Solver::Solve(const z3::expr &formula)
{
    ExprSimplifier simplifier(formula.ctx());
    z3::expr canonized = simplifier.CanonizeBoundVariables(formula);
    canonized = simplifier.PushNegations(canonized);
    canonized = simplifier.StripToplevelExistentials(canonized, true);

    FormulaTraverser<FormulaStats> traverser;
    traverser.Traverse(canonized);

    originalFormulaStats = traverser.GetData();
    if (originalFormulaStats.functionSymbols.find("concat") != originalFormulaStats.functionSymbols.end() ||
        originalFormulaStats.functionSymbols.find("extract") != originalFormulaStats.functionSymbols.end())
    {
        std::cout << "unsupported concat/extract" << std::endl;
        std::cout << "unknown" << std::endl;
        exit(1);
    }

    std::cout << originalFormulaStats << std::endl;

    for (unsigned int i = 1; i <= originalFormulaStats.maxBitWidth; i *= 2)
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
    ExprSimplifier simplifier(formula.ctx());
    z3::expr negatedFormula = simplifier.PushNegations(!formula);

    if (Solve(negatedFormula) == SAT)
    {
        return UNSAT;
    }

    return UNKNOWN;
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
    for (const auto& [varName, varBw] : originalFormulaStats.constants)
    {
        in << "(declare-const " <<  varName << " ";
        if (varBw == 0)
        {
            in << "Bool)" << std::endl;
        }
        else
        {
            in << "(_ BitVec " << std::min(bw, varBw) << "))" << std::endl;
        }
    }
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
            z3::expr_vector modelVars(formula.ctx());
            z3::expr_vector modelVals(formula.ctx());

            SMTLIBInterpreter interpreter;
            for (const auto& [varName, varBw] : originalFormulaStats.constants)
            {
                interpreter.addConstant(varName, bw == 0 ? formula.ctx().bool_sort() : formula.ctx().bv_sort(std::min(bw, varBw)));
            }

            for (const auto& [varName, varBw] : originalFormulaStats.variables)
            {
                interpreter.addConstant(varName, bw == 0 ? formula.ctx().bool_sort() : formula.ctx().bv_sort(std::min(bw, varBw)));
            }

            std::regex varRegex ("(.+)(![0-9]+)*");

            while (getline(out, line) && line != ")")
            {
                line = std::regex_replace(line, varRegex, "$1");
                std::cout << line << std::endl;

                ANTLRInputStream input(line);
                SMTLIBv2Lexer lexer(&input);
                CommonTokenStream tokens(&lexer);
                SMTLIBv2Parser parser{&tokens};

                SMTLIBv2Parser::StartContext* tree = parser.start();
                interpreter.Run(tree->script());
            }

            std::map<std::string, z3::expr> model;
            for (const auto& [name, fun] : interpreter.funDefinitions)
            {
                const auto& [args, body] = fun;
                int origBW = -1;
                if (originalFormulaStats.constants.find(name) != originalFormulaStats.constants.end())
                {
                    origBW = originalFormulaStats.constants[name];
                }
                else if (originalFormulaStats.variables.find(name) != originalFormulaStats.variables.end())
                {
                    origBW = originalFormulaStats.variables[name];
                }

                z3::expr val = changeBW(extendTerm(body), origBW);
                model.insert({name, val});
                std::cout << name << " -> " << val << std::endl;
            }

            interpreter.funDefinitions.clear();

            z3::expr origFormula = formula;
            std::cout << "Substitute into the original formula " << std::endl;
            std::cout << origFormula << std::endl;

            ExprSimplifier simplifier(formula.ctx());
            std::vector<std::string> boundVars;

            z3::expr substituted = simplifier.SubstituteExistentials(origFormula, model, boundVars);
            if (verify(substituted, "boolector"))
            {
                return SAT;
            }
        }
    }

    c.wait();

    return UNKNOWN;
}

z3::expr Solver::extendTerm(const z3::expr &e)
{
    if (e.is_numeral())
    {
        return e;
    }

    if (e.is_const())
    {
        std::string name = e.to_string();

        int origBW = -1;
        if (originalFormulaStats.constants.find(name) != originalFormulaStats.constants.end())
        {
            origBW = originalFormulaStats.constants[name];
        }
        else if (originalFormulaStats.variables.find(name) != originalFormulaStats.variables.end())
        {
            origBW = originalFormulaStats.variables[name];
        }

        if (origBW == 0)
        {
            return e;
        }

        z3::expr newVar = e.ctx().bv_const(name.c_str(), origBW);
        return newVar;
    }
    else if (e.is_var())
    {
        //TODO
        std::cout << "unsupported " << e << std::endl;
        exit(1);
    }
    else if (e.is_app())
    {
        z3::func_decl f = e.decl();
        unsigned num = e.num_args();

        z3::expr_vector arguments(e.ctx());
        for (unsigned int i = 0; i < num; i++)
        {
            arguments.push_back(extendTerm(e.arg(i)));
        }

        int newBW;
        switch (f.decl_kind())
        {
        case Z3_OP_ZERO_EXT:
            //TODO
            std::cout << "unsupported " << e << std::endl;
            exit(1);
        case Z3_OP_SIGN_EXT:
            //TODO
            std::cout << "unsupported " << e << std::endl;
            exit(1);
        case Z3_OP_ITE:
            newBW = std::max(arguments[1].get_sort().bv_size(), arguments[2].get_sort().bv_size());
            return z3::ite(arguments[0], changeBW(arguments[1], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BADD:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) + changeBW(arguments[1], newBW);
        case Z3_OP_BSUB:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) - changeBW(arguments[1], newBW);
        case Z3_OP_BAND:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) & changeBW(arguments[1], newBW);
        case Z3_OP_BOR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) | changeBW(arguments[1], newBW);
        case Z3_OP_BXOR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) ^ changeBW(arguments[1], newBW);
        case Z3_OP_BNAND:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::nand(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BNOR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::nor(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BXNOR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::xnor(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BMUL:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) * changeBW(arguments[1], newBW);
        case Z3_OP_BSDIV:
        case Z3_OP_BSDIV_I:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) / changeBW(arguments[1], newBW);
        case Z3_OP_BUDIV:
        case Z3_OP_BUDIV_I:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::udiv(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BUREM:
        case Z3_OP_BUREM_I:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::urem(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BSREM:
        case Z3_OP_BSREM_I:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::srem(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BSHL:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::shl(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BASHR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::ashr(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_BLSHR:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::lshr(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_SLT:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) < changeBW(arguments[1], newBW);
        case Z3_OP_SLEQ:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) <= changeBW(arguments[1], newBW);
        case Z3_OP_SGT:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) > changeBW(arguments[1], newBW);
        case Z3_OP_SGEQ:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) >= changeBW(arguments[1], newBW);
        case Z3_OP_ULT:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::ult(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_ULEQ:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::ule(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_UGT:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::ugt(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_UGEQ:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return z3::uge(changeBW(arguments[0], newBW), changeBW(arguments[1], newBW));
        case Z3_OP_EQ:
            newBW = std::max(arguments[0].get_sort().bv_size(), arguments[0].get_sort().bv_size());
            return changeBW(arguments[0], newBW) == changeBW(arguments[1], newBW);
        case Z3_OP_DISTINCT:
            return z3::distinct(arguments);
        case Z3_OP_BNOT:
            return ~arguments[0];
        default:
            z3::expr result = f(arguments);
            return result;
        }
    }

    return e;
}

z3::expr Solver::changeBW(const z3::expr &e, int bw)
{
    int oldBW = e.get_sort().bv_size();

    if (oldBW == bw)
    {
        return e;
    }
    else if (oldBW < bw)
    {
        return z3::sext(e, bw - oldBW);
    }
    else
    {
        return e.extract(bw - 1, 0);
    }
}


bool Solver::verify(const z3::expr& formula, std::string verifyingSolver)
{
    boost::process::opstream in;
    boost::process::ipstream out;
    boost::process::child c(boost::process::search_path(verifyingSolver), boost::process::std_out > out, boost::process::std_in < in);

    in << "(set-logic BV)" << std::endl;
    for (const auto& [varName, varBw] : originalFormulaStats.constants)
    {
        in << "(declare-const " <<  varName << " ";
        if (varBw == 0)
        {
            in << "Bool)" << std::endl;
        }
        else
        {
            in << "(_ BitVec " << varBw << "))" << std::endl;
        }
    }
    in << "(assert " << formula << ")" << std::endl;
    in << "(check-sat)" << std::endl;
    in << "(exit)" << std::endl;

    std::string line;
    std::getline(out, line);

    std::cout << "Result: " << line << std::endl;
    return line == "sat";
}
