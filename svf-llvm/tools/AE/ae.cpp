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
#include "AETestDriver.h"

#include "SVF-LLVM/PAGBuilder.h"
#include "WPA/WPAPass.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"

#include "AE/Svfexe/AbstractInterpretation.h"

#include <cassert>

using namespace SVF;
using namespace SVFUtil;

int main(int argc, char** argv)
{
    int arg_num = 0;
    int extraArgc = 3;
    char **arg_value = new char *[argc + extraArgc];
    for (; arg_num < argc; ++arg_num)
    {
        arg_value[arg_num] = argv[arg_num];
    }
    // add extra options
    arg_value[arg_num++] = (char*) "-model-consts=true";
    arg_value[arg_num++] = (char*) "-model-arrays=true";
    arg_value[arg_num++] = (char*) "-pre-field-sensitive=false";
    assert(arg_num == (argc + extraArgc) && "more extra arguments? Change the value of extraArgc");

    std::vector<std::string> moduleNameVec;
    moduleNameVec = OptionBase::parseOptions(
                        arg_num, arg_value, "Static Symbolic Execution", "[options] <input-bitcode...>"
                    );
    delete[] arg_value;
    if (runAEDomainTests())
        return 0;

    LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
    PAGBuilder builder;
    PAG* pag = builder.build();
    // Run Andersen's to resolve indirect calls, then update PAG with resolved targets.
    // The Andersen singleton will be reused inside AbstractInterpretation::runOnModule().
    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);
    builder.updateCallGraph(ander->getCallGraph());
    AbstractInterpretation& ae = AbstractInterpretation::getAEInstance();
    if (Options::BufferOverflowCheck())
        ae.addDetector(std::make_unique<BufOverflowDetector>());
    if (Options::NullDerefCheck())
        ae.addDetector(std::make_unique<NullptrDerefDetector>());
    ae.runOnModule();

    AndersenWaveDiff::releaseAndersenWaveDiff();
    LLVMModuleSet::releaseLLVMModuleSet();

    return 0;
}
