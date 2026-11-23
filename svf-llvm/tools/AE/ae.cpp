//===- ae.cpp -- Abstract Execution -------------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//

/*
 // Abstract Execution
 //
 // Author: Jiawei Wang, Xiao Cheng, Jiawei Yang, Jiawei Ren, Yulei Sui
 */
#include "AE/Svfexe/AbstractInterpretation.h"
#include "SVF-LLVM/ImpactSourceVariables.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Program.h"

#include <chrono>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string_view>
#include <vector>

using namespace SVF;
using namespace SVFUtil;

namespace
{

void runBoxPass(const std::vector<char*>& arguments)
{
    const auto ledger = Options::AEQueryLedgerFile();
    const auto post = Options::AEPostCheckFile();
    if (!std::filesystem::create_directory(ledger + ".box-may-run"))
        throw std::runtime_error("Box-May requires a fresh output path: " + ledger);
    const std::vector<std::string> outputs = {
        ledger, ledger + ".partial", ledger + ".box",
        ledger + ".box.iterations.tsv", ledger + ".box.recheck.tsv",
        ledger + ".octagon", ledger + ".octagon.iterations.tsv",
        ledger + ".octagon.recheck.tsv", post, post + ".box"
    };
    for (std::size_t index = 0; index < outputs.size(); ++index)
    {
        const auto path = std::filesystem::weakly_canonical(outputs[index]);
        if (std::filesystem::exists(std::filesystem::symlink_status(outputs[index])))
            throw std::runtime_error("Box-May output already exists: " + outputs[index]);
        for (std::size_t other = 0; other < index; ++other)
            if (path == std::filesystem::weakly_canonical(outputs[other]))
                throw std::runtime_error("Box-May output paths collide: " + outputs[index]);
    }

    const auto executable = llvm::sys::fs::getMainExecutable(arguments.front(),
        reinterpret_cast<void*>(&runBoxPass));
    const auto boxLedger = "-ae-query-ledger=" + ledger + ".box";
    const auto boxPost = "-ae-post-check=" + post + ".box";
    std::vector<llvm::StringRef> child{executable, "-ae-domain=box",
        "-ae-relational-policy=whole", "-ae-sparsity=sparse",
        "-ae-verify-query-coverage", boxLedger, boxPost};
    for (std::size_t index = 1; index < arguments.size(); ++index)
    {
        const llvm::StringRef argument(arguments[index]);
        const auto [name, value] = argument.split('=');
        (void)value;
        if (name == "-ae-domain" || name == "-ae-relational-policy" || name == "-ae-sparsity" ||
                name == "-ae-query-ledger" || name == "-ae-post-check")
        {
            if (name.size() == argument.size())
                ++index;
        }
        else if (name != "-ae-closure-box-may" && name != "-ae-ondemand" &&
                 name != "-ae-verify-query-coverage" &&
                 name != "-ae-closure-queries" && name != "-ae-closure-dependency-slice")
            child.push_back(argument);
    }
    using Clock = std::chrono::steady_clock;
    const auto start = Clock::now();
    std::string error;
    std::optional<llvm::sys::ProcessStatistics> stats;
    SVFUtil::outs() << "AE_BOX_MAY phase=box\n";
    SVFUtil::outs().flush();
    const int code = llvm::sys::ExecuteAndWait(executable, child, std::nullopt, {},
                                              0, 0, &error, nullptr, &stats);
    SVFUtil::outs() << "AE_BOX_MAY_BOX_SECONDS "
                    << std::chrono::duration<double>(Clock::now() - start).count();
    if (stats)
    {
#ifdef __APPLE__
        // LLVM forwards ru_maxrss, which Darwin reports in bytes.
        const auto peakBytes = stats->PeakMemory;
#else
        const auto peakBytes = stats->PeakMemory * 1024;
#endif
        SVFUtil::outs() << " cpu_s=" << stats->TotalTime.count() / 1e6
                        << " peak_rss_bytes=" << peakBytes;
    }
    SVFUtil::outs() << '\n';
    if (code != 0)
        throw std::runtime_error("certified Box pass failed (exit " +
                                 std::to_string(code) + "): " + error);
    SVFUtil::outs() << "AE_BOX_MAY phase=octagon\n";
    SVFUtil::outs().flush();
}

} // namespace

int main(int argc, char** argv)
{
    std::vector<char*> arguments(argv, argv + argc);
    arguments.reserve(static_cast<std::size_t>(argc) + 3);
    const auto hasOption = [&](std::string_view option)
    {
        for (int index = 1; index < argc; ++index)
        {
            const std::string_view argument(argv[index]);
            if (argument == option ||
                    (argument.size() > option.size() &&
                     argument.compare(0, option.size(), option) == 0 &&
                     argument[option.size()] == '='))
                return true;
        }
        return false;
    };
    const auto addDefault = [&](std::string_view option, char* value)
    {
        if (!hasOption(option))
            arguments.push_back(value);
    };
    addDefault("-model-consts", const_cast<char*>("-model-consts=true"));
    addDefault("-model-arrays", const_cast<char*>("-model-arrays=true"));
    addDefault("-pre-field-sensitive",
               const_cast<char*>("-pre-field-sensitive=false"));

    const std::vector<std::string> modules =
        OptionBase::parseOptions(static_cast<int>(arguments.size()),
                                 arguments.data(), "Static Symbolic Execution",
                                 "[options] <input-bitcode...>");

    if (Options::AESparsity() == AbstractInterpretation::Sparse &&
            Options::AEDomain() != AbstractInterpretation::Box &&
            !AbstractInterpretation::usesPackSSA())
    {
        std::cerr << "ae: relational sparse AE requires native Octagon packing\n";
        return 2;
    }

    if (Options::AERelationalPolicy() == AbstractInterpretation::DuetPackedRelational &&
            (Options::AEDomain() != AbstractInterpretation::Octagon ||
             Options::AESparsity() != AbstractInterpretation::Sparse ||
             Options::AEPostCheckFile().empty() ||
             std::getenv("SVF_AE_SINGLETON_PACKS")))
    {
        std::cerr << "ae: duet12 requires sparse Octagon with Post checking\n";
        return 2;
    }

    if (Options::AERelationalPolicy() == AbstractInterpretation::SpePackedRelational &&
            (Options::AEDomain() != AbstractInterpretation::Octagon ||
             Options::AESparsity() != AbstractInterpretation::Dense ||
             Options::AEQueryLedgerFile().empty() || Options::AEQueryInputID().empty() ||
             Options::AEPostCheckFile().empty() || std::getenv("SVF_AE_SINGLETON_PACKS")))
    {
        std::cerr << "ae: spe17-pack requires dense Octagon, a query inventory and Post checking\n";
        return 2;
    }

    const bool guided = AbstractInterpretation::usesOnDemand();
    if (guided || Options::AEVerifyQueryCoverage())
    {
        if (Options::AEQueryLedgerFile().empty() || Options::AEPostCheckFile().empty() ||
                Options::AEQueryInputID().empty() || std::getenv("SVF_AE_SKIP_POST_CHECK") ||
                std::getenv("SVF_AE_PACK_ONLY"))
        {
            std::cerr << "ae: query certification requires a ledger, input ID and Post replay\n";
            return 2;
        }
    }
    if (guided)
    {
        const auto policy = Options::AERelationalPolicy();
        const bool closure = policy == AbstractInterpretation::ClosurePackedRelational;
        const bool duet = policy == AbstractInterpretation::DuetPackedRelational;
        const bool spe = policy == AbstractInterpretation::SpePackedRelational;
        if (Options::AEDomain() != AbstractInterpretation::Octagon ||
                (!closure && !duet && !spe) || (Options::AEClosureBoxMay() && !closure) ||
                (!spe && Options::AESparsity() != AbstractInterpretation::Sparse) ||
                Options::AEClosureQueries() || Options::AEClosureDependencySlice() ||
                std::getenv("SVF_AE_SINGLETON_PACKS") ||
                std::getenv("SVF_AE_VERIFY_PACKED_EXECUTOR") ||
                std::getenv("SVF_AE_L4_NAMES") || std::getenv("SVF_AE_L4_STATES"))
        {
            std::cerr << "ae: OnDemand requires a supported full Octagon packing policy\n";
            return 2;
        }
        try
        {
            runBoxPass(arguments);
        }
        catch (const std::exception& error)
        {
            SVFUtil::errs() << "AE_BOX_MAY status=unavailable: " << error.what() << '\n';
            return 2;
        }
    }

    LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(modules);
    SVFIRBuilder builder;
    SVFIR* pag = builder.build();
    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);
    builder.updateCallGraph(ander->getCallGraph());

    registerImpactSourceVariables();

    AbstractInterpretation& ae = AbstractInterpretation::getAEInstance();
    if (Options::BufferOverflowCheck())
        ae.addDetector(std::make_unique<BufOverflowDetector>());
    if (Options::NullDerefCheck())
        ae.addDetector(std::make_unique<NullptrDerefDetector>());
    int status = 0;
    try
    {
        ae.runOnModule();
    }
    catch (const std::exception& error)
    {
        SVFUtil::errs() << (guided ? "AE_BOX_MAY status=unavailable: " : "ae: ")
                        << error.what() << '\n';
        status = 2;
    }

    // L4 names: SVF IDs are per-process allocation order, so map them to
    // LLVM semantic names in the same process. Runs after every timed phase.
    if (const char* namesPath = std::getenv("SVF_AE_L4_NAMES"); namesPath && status == 0)
    {
        const auto start = std::chrono::steady_clock::now();
        std::ofstream names(namesPath, std::ios::out | std::ios::trunc);
        const auto semanticName = [](const llvm::Value* value)
        {
            std::string text;
            llvm::raw_string_ostream stream(text);
            if (const auto* instruction = llvm::dyn_cast<llvm::Instruction>(value))
                stream << LLVMModuleSet::instructionSemanticSite(instruction);
            else if (const auto* argument = llvm::dyn_cast<llvm::Argument>(value))
                stream << "fn=" << argument->getParent()->getName() << ":arg=" << argument->getArgNo();
            else if (const auto* global = llvm::dyn_cast<llvm::GlobalValue>(value))
            {
                stream << "global=";
                global->printAsOperand(stream, false);
            }
            else if (llvm::isa<llvm::Constant>(value))
            {
                stream << "const=";
                value->printAsOperand(stream, true);
            }
            else
                stream << "other=";
            stream.flush();
            for (char& c : text)
                if (c == '\t' || c == '\n')
                    c = ' ';
            return text;
        };
        // Integer bit width lets L4 treat a full type range as no information.
        const auto bitWidth = [](const llvm::Type* type)
        {
            return type->isIntegerTy() ? std::to_string(type->getIntegerBitWidth()) : std::string("-");
        };
        LLVMModuleSet* set = LLVMModuleSet::getLLVMModuleSet();
        for (const auto& [value, id] : set->valSyms())
            if (value)
                names << "v\t" << id << '\t' << bitWidth(value->getType()) << '\t'
                      << semanticName(value) << '\n';
        for (const auto& [value, id] : set->objSyms())
            if (value)
                names << "o\t" << id << "\t-\t" << semanticName(value) << '\n';
        names.close();
        SVFUtil::outs() << "AE_L4_NAMES_SECONDS "
                        << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count()
                        << '\n';
        SVFUtil::outs().flush();
    }

    AndersenWaveDiff::releaseAndersenWaveDiff();
    LLVMModuleSet::releaseLLVMModuleSet();
    return status;
}
