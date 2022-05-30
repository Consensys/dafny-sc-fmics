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

include "../utils/NonNativeTypes.dfy"
include "./Contract.dfy" 
include "../utils/TestUtils.dfy"

import opened NonNativeTypes 

import T = TestUtils 

/** A message. */
datatype Msg = Msg(sender: Account, value: uint256) 

/** Environment to implement wrapper to get address.send */
datatype Try<T> = Success(v: T) | Revert()

type Address = Account  

/** Can be notified and call a C2. */
class C1 extends Account {

    var id: string 

    constructor(n: string) {
        id := n;
    }

    /** If enough gas provided, call back `from` to transfer.   */
    method notify(from: C2, tK: TokenRevert, amount: uint256, msg: Msg, gas: nat) returns (g:nat, r: Try<()>)
        decreases gas 
        modifies tK 
    {
        if gas >= 1 {
            print T.MAGENTA, id, " calls ", from.id, ".help  gas left:", gas - 1, T.RESET, "\n";
            g, r := from.help(this, tK, amount, msg, gas - 1);
        } else {
            print T.MAGENTA, id, ".notify Reverting ", "not enough gas", T.RESET, "\n";
            g, r := 0, Revert();
        }
    }
}

/** C2 can call transfer. */
class C2 extends Account {

    var id: string 

    constructor(n: string) {
        id := n;
    }

    /** Transfer some amount of tk is enough gas.  */
    method help(to: C1, tK: TokenRevert, amount: uint256, msg: Msg, gas: nat) returns (g:nat, r: Try<()>)
        decreases gas 
        modifies tK 
    {
        if gas >= 1 {
            print T.BLUE, id, " calls ", tK.id, ".transfer for ", amount, " to ", to.id, " gas left:", gas - 1, T.RESET, "\n";
            g, r := tK.transfer(this, to, amount, msg, gas - 1);
        } else {
            print T.BLUE, id, ".help Reverting ", "not enough gas", T.RESET, "\n";
            g, r := 0, Revert();
        }
    }
}

/**
 *  The token example with a re-entrancy vulnerability.
 */
class TokenRevert extends Account {

    var id: string 

    const minter: Address 

    var balances : map<Address, uint256>

    //  Track minted tokens.
    var totalAmount: nat  

    var transferNumber: nat 

    /** Initialise contract.  */
    constructor(name: string, msg: Msg) 
        ensures balance == msg.value
        ensures minter == msg.sender
    {
        id := name;
        isContract := true;
        minter := msg.sender;
        balances := map[]; 
        balance := msg.value;
        totalAmount := 0;
        transferNumber := 0;
        print T.YELLOW, "Token K : ", name, " created", T.RESET, "\n";
    }

    /**
     *  Transfer some tokens from an account to another.
     *
     *  @param  from    Source Address.
     *  @param  to      Target Address.
     *  @param  amount  The amount to be transfered from `from` to `to`.
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call.
     */
    method transfer(from: C2, to: C1, amount: uint256, msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
        decreases gas
        modifies this
    {
        if !(from in balances && balances[from] >= amount && msg.sender == from && gas >= 1
            && (to !in balances || balances[to] as nat + amount as nat <= MAX_UINT256) ) {
            print T.YELLOW, this.id, ".transfer#", transferNumber + 1, " reverting ", "gas: ", gas, T.RESET, "\n";
            return (if gas >= 1 then gas - 1 else 0), Revert(); 
        } 
        transferNumber := transferNumber + 1;
        var n := transferNumber;
        print T.YELLOW, this.id, ".transfer#", n, " from ", from.id, " for ", amount, " to ", to.id, T.RESET, "\n";
        var newAmount := balances[from] - amount;
        balances := balances[to := (if to in balances then balances[to] else 0) + amount] ;
        print T.YELLOW, this.id, " notifies ", to.id, T.RESET, "\n";
        g, r := to.notify(from, this, amount, msg, gas - 1);
        balances := balances[from := newAmount];
        print T.YELLOW, this.id, ".transfer#", n , " completed", T.RESET, "\n";
    }  

    /**
     *  Mint some new tokens.
     *
     *  @param  to      Target Address.
     *  @param  amount  The amount to receiving the newly minted tokens
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call.
     */
    method mint(to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
        ensures r.Success? ==> totalAmount == old(totalAmount) + amount as nat
        ensures r.Success? ==> to in balances
        ensures r.Revert? <==> !(msg.sender == minter && gas >= 1 && (to !in old(balances) ||  old(balances[to]) as nat + amount as nat <= MAX_UINT256))
        //  state unchanged on a revert.
        ensures r.Revert? ==> balances == old(balances) 
        ensures g == 0 || g <= gas - 1

        modifies this`balances, this`totalAmount
        decreases gas 
    {
        if !(msg.sender == minter && gas >= 1 && (to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256)) {
            print T.YELLOW, this.id, " mint reverts ", "gas: ", gas, T.RESET, "\n";
            return (if gas >= 1 then gas - 1 else 0), Revert();
        }
        balances := balances[to := (if to in balances then balances[to] else 0) + amount]; 
        print T.YELLOW, "Token K : ", this.id, " mints ", amount, T.RESET, "\n";

        //  The total amount increases.
        totalAmount := totalAmount + amount as nat;
        g, r := gas - 1, Success(());
    }
}

/**
 *  Example to demonstrate re-entrancy.
 *  
 *  @note   To run use `dafny /noVerify /compile:4`
 *  
 */
method Main() 
{
    print T.GREEN,"This is an example of exploit of re-entrancy", T.RESET, "\n";

    //  Contract c1 can be notified.
    var c1 := new C1("BadGuy1");
    //  Contract c2 can transfer
    var c2 := new C2("BadGuy2");

    //  c3 is the owner of the token contract.
    var c3 := new C1("Minter");
    //  Create a Token contract
    var tk := new TokenRevert("TokenK", Msg(c3, 0));

    //  c3 mints 200 tokens for c2, 
    var g1, r1 := tk.mint(to := c2, amount := 200, msg := Msg(c3, 0), gas := 10);

    print T.GREEN,"Contract ", tk.id, " total amount:", tk.totalAmount, T.RESET, "\n";
    if c2 in tk.balances {
        print "c2.bal initially: ", tk.balances[c2], "\n";
    }
    
    var g2, r2 := tk.transfer(from := c2, to := c1, amount := 200, msg := Msg(c2, 0), gas := g1);
    
    print T.GREEN,"Contract ", tk.id, " total amount:", tk.totalAmount, T.RESET, "\n";
    if c1 in tk.balances && c2 in tk.balances {
        print "c1.bal final: ", tk.balances[c1], "\n";
        print  "c2.bal final: ", tk.balances[c2], "\n";
        print T.RED, "c1.bal + c2.bal: ", tk.balances[c1] as nat + tk.balances[c2] as nat, T.RESET, "\n";
    }
}
