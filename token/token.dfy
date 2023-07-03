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

type Address = Account  

/**
 *  The Token contract example from:
 *  Rich Specifications for Ethereum Smart Contract Verification, Christian Bräm et al.
 *  @link{ttps://arxiv.org/abs/2104.10274}
 */

/**
 *  The token example with a re-entrancy vulnerability.
 */
class Token extends Account {

    const minter: Address 
    var balances : map<Address, uint256>

    ghost var totalAmount: nat  

    /** 
     *  Contract invariant. 
     *  The total amount is preserved by each method call.
     */
    predicate GInv() 
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
     *  @param  msg     The `msg` content.
     *  @param  gas     The gas allocated to the execution.
     *  @returns        The gas left after executing the call.
     */
    method transfer(from: Address, to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat)
        requires from in balances
        requires gas >= 1
        requires msg.value == 0;
        requires balances[from] >= amount && msg.sender == from 
        requires to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256
        requires msg.sender == from 
        requires GInv()

        ensures GInv()
        ensures from in balances && balances[from] == old(balances[from]) - amount
        ensures to in balances 
        ensures to != from ==> balances[to] >= amount
        ensures to == from ==> balances == old(balances)

        modifies this
    {
        balance := balance + msg.value;
        var newAmount: uint256 := balances[from] - amount ;
        //  Use lemma
        mapAddSub(balances, from, to, amount);
        balances := balances[to := (if to in balances then balances[to] else 0) + amount] ;
        balances := balances[from := newAmount];
        g := gas - 1;
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
    method mint(to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat)
        requires msg.sender == minter
        requires gas >= 1
        requires to !in balances ||  balances[to] as nat + amount as nat <= MAX_UINT256
        requires GInv()

        ensures totalAmount == old(totalAmount) + amount as nat
        ensures GInv()

        modifies this`balances, this`totalAmount
    {
        //  Use lemma.
        mapAdd(balances, to, amount as nat);
        balances := balances[to := (if to in balances then balances[to] else 0) + amount]; 

        //  The total amount increases.
        totalAmount := totalAmount + amount as nat;
        g := gas - 1;
    }

   
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
    *  If the value `m` at key `k` is incremented by `v` then sum(m) is incremented by `v` too.
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




