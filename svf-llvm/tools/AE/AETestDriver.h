//===- AETestDriver.h -- Abstract Execution self-tests -------------------//
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
 // Abstract Execution self-tests
 //
 // Author: Jiawei Wang, Xiao Cheng, Jiawei Yang, Jiawei Ren, Yulei Sui
 */
#ifndef SVF_AE_TEST_DRIVER_H
#define SVF_AE_TEST_DRIVER_H

namespace SVF
{

/// Run the selected CLI self-test after parsing options. Return false in analysis mode.
bool runAEDomainTests();

} // namespace SVF

#endif // SVF_AE_TEST_DRIVER_H
