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

import opened NonNativeTypes 

/** A message. */
datatype Msg = Msg(sender: Account, value: uint256) 

/** Environment to implement wrapper to get address.send */
datatype Try<T> = Success(v: T) | Revert()

type Address = Account  

/**
 *  The Token contract with revert. Example from:
 *  Rich Specifications for Ethereum Smart Contract Verification, Christian Bräm et al.
 *  @link{ttps://arxiv.org/abs/2104.10274}
 */

/**
 *  The token example with a re-entrancy vulnerability.
 */
class TokenRevertExternal extends Account {

    const minter: Address 
    var balances : map<Address, uint256>

    //  Track minted tokens.
    ghost var totalAmount: nat  

    /** 
     *  Contract invariant. 
     *  The total amount is preserved by each method call.
     */
    ghost predicate GInv()
        reads this`totalAmount, this`balances
    {
        totalAmount == sum(balances)
    }

    /** Initialise contract.  */
    constructor(msg: Msg) 
        ensures GInv()
        ensures balance == msg.value
        ensures minter == msg.sender
    {
        isContract := true;
        minter := msg.sender;
        balances := map[]; 
        balance := msg.value;
        totalAmount := 0;
    }

    /**
     *  Transfer some tokens from an account to another.
     *
     *  @param  from    Source Address.
     *  @param  to      Target Address.
     *  @param  amount  The amount to be transfered from `from` to `to`.
     *  @param  msg     The message value.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call and the status of the call.
     */
    method transfer(from: Address, to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat, r: Try<()>)

        requires GInv()
        ensures 
            r.Success? <==>  
            (from in old(balances) 
            && old(balances[from]) >= amount 
            && msg.sender == from 
            && gas >= 1 
            && (to !in old(balances) || old(balances[to]) as nat + amount as nat <= MAX_UINT256)) 
        /** State is unchanged on an revert. */
        ensures r.Revert? ==> balances == old(balances) 
        ensures g == 0 || g <= gas - 1
        ensures GInv()

        decreases gas
        modifies this
    {
        if !(from in balances && balances[from] >= amount && msg.sender == from && gas >= 1
            && (to !in balances || balances[to] as nat + amount as nat <= MAX_UINT256) ) {
            return (if gas >= 1 then gas - 1 else 0), Revert(); 
        } 
        var newAmount := balances[from] - amount;
        mapAddSub(balances, from, to, amount);
        balances := balances[to := (if to in balances then balances[to] else 0) + amount] ;
        //assert GInv();
        balances := balances[from := newAmount];
        assert GInv();

        //  If we swap the line above and the externalCall, we cannot prove invariance of GInv()
        //  At this location GInv() must hold which puts a restriction on where external calls
        //  can occur.
        var g1, r1 := externalCall(gas - 1);  // to.notify( from, amount );
        //balances := balances[from := newAmount];

        assert g1 == 0 || g1 <= gas - 1;
        //  We can choose to propagate or not the failure of external call. Here choose not to.
        g, r := (if g1 >= 1 then g1 - 1 else 0), Success(());
    }  



    /**
     *  Mint some new tokens.
     *
     *  @param  to      Target Address.
     *  @param  amount  The amount to receiving the newly minted tokens
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call and the status of the call.
     */
    method mint(to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures r.Success? ==> totalAmount == old(totalAmount) + amount as nat
        ensures r.Revert? <==> !(msg.sender == minter && gas >= 1 && (to !in old(balances) ||  old(balances[to]) as nat + amount as nat <= MAX_UINT256))
        //  state unchanged on a revert.
        ensures r.Revert? ==> balances == old(balances) 
        ensures g == 0 || g <= gas - 1
        ensures GInv()

        modifies this`balances, this`totalAmount
        decreases gas 
    {
        if !(msg.sender == minter && gas >= 1 && (to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256)) {
            return (if gas >= 1 then gas - 1 else 0), Revert();
        }
        //  Use lemma.
        mapAdd(balances, to, amount as nat);
        balances := balances[to := (if to in balances then balances[to] else 0) + amount]; 

        //  The total amount increases.
        totalAmount := totalAmount + amount as nat;
        g, r := gas - 1, Success(());
    }


    /**
     *  Simulate a potential re-entrant call from an externalCall.
     *  
     *  @param  gas The gas allocated to this call.
     *  @returns    The gas left after execution of the call and the status of the call.
     *
     *  @note       The state variables of the contract can only be modified by 
     *              calls to mint and transfer.
     */
    method externalCall(gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures GInv()
        ensures g == 0 || g <= gas - 1
        modifies this
        decreases gas 
    {
        g := gas; 
        //  Havoc `k` to introduce non-determinism.
        var k: nat := havoc();
        //  Depending on the value of k % 3, re-entrant call or not or another external call.
        if k % 3 == 0 && g >= 1 {
            //  re-entrant call to transfer.
            var from: Address := havoc();
            var to: Address := havoc();
            var amount: uint256 := havoc(); 
            var msg: Msg := havoc();
            g, r := transfer(from, to, amount, msg, g - 1);
        } else if k % 3 == 1 && g >= 1 {
            //  re-entrant call to mint. 
            var to: Address := havoc();
            var amount: uint256 := havoc();
            var msg: Msg := havoc();
            g, r := mint(to, amount, msg, g - 1);
        } 
        //  k % 3 == 2, no re-entrant call.
        //  Possible new external call
        var b:bool := havoc();
        if b && g >= 1 {
            //  external call makes an external call. 
            g, r := externalCall(g - 1);
        } else {
            //  external call does not make another external call. 
            g := if gas >= 1 then gas - 1 else 0;
            r := havoc();
        }
    }

    /** Havoc a given type. */
    method {:extern} havoc<T>() returns (a: T)
}



//  Helper functions

/** Abstract specification of sum for maps. 
    *  
    *  @param      m   A map.
    *  @returns    The sum of the elements in the map.
    */
function sum(m: map<Address, uint256>): nat
    ensures sum(map[]) == 0

/**
    *  Add a number to a map value.
    *  
    *  @param  m   A map.
    *  @param  k   A key.
    *  @param  v   A value. 
    *
    *  If the value at key `k` is incremented by `v` then sum(m) is incremented by `v` too.
    */
lemma mapAdd(m: map<Address, uint256>, k: Address, v: nat)
    requires (if k in m then m[k] else 0) as nat + v <= MAX_UINT256
    //  m ++ [k, v] is m with the value at k incremented by v (0 is not in key)
    //  sum(m ++ [k,v]) == sum(m) + v 
    ensures sum(m[k := ((if k in m then m[k] else 0) as nat + v) as uint256]) == sum(m) + v

/**
    *  Transfer from a key to another (or same) key.
    *
    *  @param  m   A map.
    *  @param  k1  A key,
    *  @param  k2  A key.
    *  @param  v   A value.
    *
    *  Transfering `v` from key `k1` to key k2` preserves sum(m). 
    */
lemma mapAddSub(m: map<Address, uint256>, k1: Address, k2: Address, v: uint256)
    requires k1 in m 
    requires m[k1] >= v 
    requires  (if k2 in m then m[k2] else 0) as nat + v as nat <= MAX_UINT256
    //  sum(m ++ [k2, v] ++ [k1, -v]) == sum(v)
    ensures sum(m[k2 := ((if k2 in m then m[k2] else 0) + v) as uint256][k1 := m[k1] - v]) == sum(m)
    ensures k1 == k2 ==>  m[k2 := ((if k2 in m then m[k2] else 0) + v) as uint256][k1 := m[k1] - v] == m 




