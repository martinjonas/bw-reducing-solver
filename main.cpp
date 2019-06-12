#include <iostream>
#include <string>
#include <z3++.h>
#include <cmath>
#include <fstream>
#include <cstdio>
#include <regex>
#include <unistd.h>
#include <climits>
#include <getopt.h>


#include "FormulaStats.h"
#include "FormulaTraverser.h"
#include "FormulaReducer.h"
#include "ExprSimplifier.h"

using namespace std;
using namespace z3;

const std::string boolectorPath = "/tmp/boolector";
std::string verifierPath = "/tmp/boolector";

enum Result { SAT, UNSAT, UNKNOWN };

FormulaStats formulaStats;

//TODO: Implementovat!!!
bool substZeroes = false;
bool makeQF = false;
bool dual = false;
bool zeroExtend = false;
bool keepSign = false;

Result negateResult(const Result& result)
{
    switch (result)
    {
    case SAT:
        return UNSAT;
    case UNSAT:
        return SAT;
    default:
        return UNKNOWN;
    }
}

std::string string_replace(const std::string& str, const std::string& match,
        const std::string& replacement, unsigned int max_replacements = UINT_MAX)
{
    size_t pos = 0;
    std::string newstr = str;
    unsigned int replacements = 0;
    while ((pos = newstr.find(match, pos)) != std::string::npos
            && replacements < max_replacements)
    {
         newstr.replace(pos, match.length(), replacement);
         pos += replacement.length();
         replacements++;
    }
    return newstr;
}

Result solve(std::string &fileName)
{
    std::string logFile = std::tmpnam(nullptr);
    std::system((verifierPath + " " + fileName + " > " + logFile).c_str());
    Result result = UNKNOWN;
    std::string resultLine;
    auto resultStream = ifstream(logFile);
    getline(resultStream, resultLine);
    std::remove(logFile.c_str());

    if (resultLine == "sat") result = SAT;
    else if (resultLine == "unsat") result = UNSAT;

    return result;
}

std::string getReducedFormula(z3::solver &s, z3::expr &e, unsigned int bw)
{
    std::string newName = std::tmpnam(nullptr);

    std::cout << "Reducing to " << bw << " bits" << std::endl;

    FormulaReducer reducer;
    s.reset();
    s.add(reducer.Reduce(e, bw, keepSign));

    std::cout << "Writing reduced formula to file" << std::endl;

    std::ofstream file(newName.c_str());
    if (file.is_open())
    {
        file << "(set-logic BV)" << std::endl;
        file << "(set-option :produce-models true)" << std::endl;
        file << "(check-sat)" << std::endl;
        file << "(get-model)" << std::endl;
        file.close();
    }

    return newName;
}

std::string canonizeFormula(z3::solver &s, z3::expr &e)
{
    std::cout << "Canonizing bound variables" << std::endl;

    ExprSimplifier simplifier(e.ctx());

    std::string canonizedName = std::tmpnam(nullptr);
    e = simplifier.CanonizeBoundVariables(e);
    s.reset();
    s.add(e);

    e = s.assertions()[0];
    e = simplifier.PushNegations(e);
    e = simplifier.StripToplevelExistentials(e, true);
    s.reset();
    s.add(e);

    std::cout << "Writing canonized formula to file" << std::endl;

    std::ofstream canonizedFile(canonizedName.c_str());
    if (canonizedFile.is_open())
    {
        canonizedFile << "(set-logic BV)" << std::endl;
        canonizedFile << s << std::endl;
        canonizedFile << "(check-sat)" << std::endl;
        canonizedFile.close();
    }

    return canonizedName;
}

Result solveReduced(const std::string& originalName, const std::string& reducedName, unsigned int bw)
{
    std::cout << "Running boolector" << std::endl;

    std::string resultFilePath = std::tmpnam(nullptr);
    std::system((boolectorPath + " -d --quant:dual=0 " + reducedName + " > " + resultFilePath).c_str());

    auto resultFile = std::ifstream(resultFilePath);

    std::string line;
    std::getline(resultFile, line);

    if (line == "sat")
    {
        std::cout << "The reduced formula is SAT" << std::endl;

        auto inputFile = std::ifstream(originalName);
        std::string inputFileString((std::istreambuf_iterator<char>(inputFile)),
                                    std::istreambuf_iterator<char>());

        //rename declare-fun, so the variable in it is not replaced later
        inputFileString = string_replace(inputFileString, "(declare-fun ", "(declare-fun_");

        getline(resultFile, line);
        //the solver has returned an assignment to some variables; use it
        if (line == "(model")
        {
            std::cout << "The model is available:" << std::endl;

	    //replace constants of BW bw by the original BW
            std::regex bitWidthRegex ("\\(_ bv(\\d+) " + std::to_string(bw) + "\\)");

            std::regex varRegex ("(\\w+)!(\\d|!)+(\\s|\\)|$)");
            while (getline(resultFile, line) && line != ")")
            {
                line = line.substr(14, line.size() - 15); //strip "  (define-fun "
                size_t spacePos = line.find(' ');

                std::string varName = line.substr(0, spacePos);
                size_t exclamationPos = varName.find('!');
                varName = varName.substr(0, exclamationPos); //"x!0!1!0" -> x

                std::string body = line.substr(spacePos + 1 + 16); //also strip " () (_ BitVec _) "
                if (zeroExtend)
                {
                    body = std::regex_replace(body, bitWidthRegex, "((_ zero_extend " + std::to_string(formulaStats.maxBitWidth - bw) + ") $0)");
                }
                else
                {
                    body = std::regex_replace(body, bitWidthRegex, "((_ sign_extend " + std::to_string(formulaStats.maxBitWidth - bw) + ") $0)");
                }
                body = std::regex_replace(body, varRegex, "$1$3");

                inputFileString = string_replace(inputFileString, " " + varName + " ", " " + body + " ");
                inputFileString = string_replace(inputFileString, " " + varName + "\n", " " + body + " ");
                inputFileString = string_replace(inputFileString, " " + varName + ")", " " + body + ")");
                std::cout << "  " << varName << " -> " << body << std::endl;
            }
        }

        inputFileString = string_replace(inputFileString, "(declare-fun_", "(declare-fun ");

        std::cout << "Writing substituted formula into an external file" << std::endl;
        std::string substName = std::tmpnam(nullptr);

        std::ofstream file(substName);
        if (file.is_open())
        {
            file << inputFileString << std::endl;
	    std::cout << inputFileString << std::endl;
	    file.close();
        }

        z3::context ctx;
        z3::solver s(ctx);
        s.from_file(substName.c_str());

        if (s.assertions().size() == 0)
        {
            std::cout << "unknown" << std::endl;
            exit(1);
        }

        std::string qfSubstName = std::tmpnam(nullptr);

        if (makeQF)
        {
            // convert the formula to a quantifier free
            // i.e. 1) negate the formula and convert existential variables to uninterpreted constants
            //      2) replace all remaining universal variables by 0
            z3::expr qf_e = s.assertions().size() == 1 ? s.assertions()[0] : mk_and(s.assertions());
            ExprSimplifier simplifier(ctx);
            qf_e = simplifier.PushNegations(qf_e);
            qf_e = simplifier.RemoveExistentials(qf_e);
            qf_e = !qf_e;
            s.reset();
            s.add(qf_e);
        }

        std::ofstream qfSubstFile(qfSubstName.c_str());
        if (qfSubstFile.is_open())
        {
            qfSubstFile << (makeQF ? "(set-logic QF_BV)" : "(set-logic BV)") << std::endl;
            qfSubstFile << s << std::endl;
            qfSubstFile << "(check-sat)" << std::endl;
            qfSubstFile.close();
	    std::cout << s << std::endl;
        }

        std::cout << "Running verifier" << std::endl;

        auto result = solve(qfSubstName);
        if (makeQF) result = negateResult(result);

        switch (result)
        {
        case SAT:
            std::cout << "Final check is SAT" << std::endl;
            return SAT;
        case UNSAT:
            std::cout << "Final check is UNSAT" << std::endl;
        default:
            std::cout << "The result is neither sat nor unsat" << std::endl;
        }
        return UNKNOWN;
    }
    else if (line == "unsat")
    {
        std::cout << "The reduced formula is UNSAT" << std::endl;
        if (bw >= 6)
        {
            std::cout << "... giving up; the formula is probably UNSAT" << std::endl;
            std::cout << "unknown" << std::endl;
            exit(0);
        }
        return UNKNOWN;
    }

    std::cout << "The result is neither sat nor unsat" << std::endl;
    return UNKNOWN;
}

int main(int argc, char* argv[])
{
    static struct option long_options[] = {
        {"dual", no_argument, 0, 'd' },
        {"makeqf", no_argument, 0, 'q' },
        {"zeroextend", no_argument, 0, 'z' },
        {"keepsign", no_argument, 0, 'k' },
        {"verifier", required_argument, 0, 'v' },
	{0,           0,                 0,  0   }
    };

    std::string filename;

    int opt = 0;
    int long_index = 0;
    while ((opt = getopt_long(argc, argv,"dqzkv", long_options, &long_index )) != -1) {
	switch (opt) {
	case 'd':
            dual = true;
	    break;
	case 'q':
            makeQF = true;
	    break;
	case 'z':
            zeroExtend = true;
	    break;
	case 'k':
            keepSign = true;
	    break;
	case 'v':
        {
            string optionString(optarg);
            verifierPath = optionString;
            break;
	}
	default:
	    std::cout << "Invalid arguments" << std::endl << std::endl;
            std::cout << "Usage: formulaReducer filename [--dual, --makeqf, --zeroextend]" << std::endl;
	    return 1;
	}
    }

    if (optind < argc)
    {
	filename = std::string(argv[optind]);
    }
    else
    {
	std::cout << "Filename required" << std::endl;
        std::cout << "Usage: formulaReducer filename [--dual, --makeqf, --zeroextend]" << std::endl;
	return 1;
    }

    z3::context ctx;
    z3::solver s(ctx);
    s.from_file(filename.c_str());
    z3::expr e = s.assertions().size() == 1 ? s.assertions()[0] : mk_and(s.assertions());

    FormulaTraverser<FormulaStats> traverser;
    traverser.Traverse(e);

    formulaStats = traverser.GetData();
    if (formulaStats.functionSymbols.find("concat") != formulaStats.functionSymbols.end() ||
        formulaStats.functionSymbols.find("extract") != formulaStats.functionSymbols.end())
    {
        std::cout << "unsupported concat/extract" << std::endl;
        std::cout << "unknown" << std::endl;
        exit(1);
    }

    // run the algorithm on a negated formula
    if (dual)
    {
        if (!formulaStats.constants.empty())
        {
            //convert the formula to a sentence
            std::cout << "Adding implicit quantifiers" << std::endl;

            z3::expr_vector quantified(e.ctx());
            for (const auto& c : formulaStats.constantASTs)
            {
                quantified.push_back(z3::expr(e.ctx(), c));
            }
            e = z3::exists(quantified, e);
        }
        std::cout << "Negating input formula" << std::endl;
        e = !e;
    }

    std::string canonizedName = canonizeFormula(s, e);

    s.reset();
    s.from_file(canonizedName.c_str());

    for (unsigned int i = 2; i <= formulaStats.maxBitWidth; i += 2)
    {
        std::cout << "---" << std::endl;
        std::string newName = getReducedFormula(s, e, i);

        switch (solveReduced(canonizedName, newName, i))
        {
        case SAT:
            std::cout << (dual ? "unsat" : "sat") << std::endl;
            return 0;
        case UNSAT:
            std::cout << (dual ? "sat" : "unsat") << std::endl;
            return 0;
        default:
            break;
        }
        std::remove(newName.c_str());
    }
    std::remove(canonizedName.c_str());
    std::cout << "unknown" << std::endl;
    return 0;
}
