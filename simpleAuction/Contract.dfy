/*
 * Copyright 2021 ConsenSys Software Inc.
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

include "../utils/NonNativeTypes.dfy"

import opened NonNativeTypes

/** A message. */
datatype Msg = Msg(sender: Account, value: uint256) 

/** A block. */
datatype Block = Block(timestamp: uint256, number: uint256) 

type Address = Account  

/** Provide a balance. */
trait {:termination false} Account { 
    /** Balance of the account. */  
    var balance : uint256

    /** Type of account. */
    const isContract: bool

    /**
     *  Transfer some ETH from `msgSender` to `this`.
     *
     *  @param  sourceSender    A source account (to be debited).
     *  @param  amount          The amount to be transfered from `msgSender` to `this`.
     */
    method transfer(sourceAccount: Account, amount : uint256, gas: nat) returns (g: nat)
        requires sourceAccount.balance >= amount 
        requires this != sourceAccount 
        requires balance as nat + amount as nat <= MAX_UINT256
        requires gas >= 1

        ensures balance == old(balance) + amount
        ensures sourceAccount.balance == old(sourceAccount.balance) - amount
        ensures g <= gas - 1

        modifies this`balance, sourceAccount`balance
    {
        sourceAccount.balance := sourceAccount.balance - amount;
        balance := balance + amount;
        g := gas - 1;
    } 

    /** Helper to be used replicating `payable` solidity functions within K classes that extend Account. */
    method processMsgValue(msg: Msg, gas: nat) returns (g: nat)
        requires this != msg.sender 
        requires gas >= 1
        requires msg.sender.balance >= msg.value
        requires balance as nat + msg.value as nat <= MAX_UINT256 as nat

        ensures msg.sender.balance == old(msg.sender.balance) - msg.value
        ensures balance == old(balance) + msg.value
        ensures g <= gas - 1
        modifies this`balance, msg.sender`balance
    {
        g := transfer(msg.sender, msg.value, gas);
    }

}

/** A user account. */
class UserAccount extends Account {

    constructor(initialBal: uint256) 
        ensures balance == initialBal
    {
        balance := initialBal;
        isContract := false;
    }
}

