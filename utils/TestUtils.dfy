/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

/**
 *  Provide simple functions to set up tests.
 */
module TestUtils  { 

    /**
     *  Test result (similar to a Try).
     */
    datatype TestStatus =
            Success()
        |   Failure(msg: string)
    {
        function method IsFailure(): bool { Failure? }
        function method PropagateFailure(): TestStatus { this }
    }

    /**
     *  C# strings for colour selection.
     */
    const RED := "\u001B[31m"
    const GREEN := "\u001B[32m"
    const YELLOW := "\u001B[33m"
    const BLUE := "\u001B[34m"
    const MAGENTA := "\u001B[35m"
    const RESET := "\u001B[0m"

    /**
     *  Build a test result.
     */
    function method makeTest(b: bool): TestStatus 
    {
        if b then 
            Success()
        else 
            Failure("failed")
    }

    /**
     *  Print test results in colour.
     *
     *  @param  t       A test.
     *  @param  testId  The Id of the test (message/title).
     */
    method printTestResult(t: TestStatus, testId: string)
    {
         if (t.Success?) {
            print GREEN + "[Success] " + RESET + testId + "\n";
        } else {
            print RED + "[Fail] " + RESET + testId + " Msg:" + t.msg + "\n";
        }
    }

}