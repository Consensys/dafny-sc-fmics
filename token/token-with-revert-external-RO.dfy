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
 * This file reimplements the token contract + revert + external calls,
 * but in this case transferRO() makes a Read-only external call, which
 * is modelled as a tree of possibly recursive R/O external calls.
 *
 * Ultimately it's of little apparent interest because the difference is minimal:
 * the getBalance() R/O (re-)entry point still requires GInv() so that it can have
 * an accurate read of balances, therefore externalROcall() also requires GInv(),
 * therefore transferRO() still needs to comply with the CEI pattern.
 * In other words, and as discussed in our paper, CEI still is needed with R/O
 * external calls to avoid read-only reentrancy attacks.
 *
 * The more interesting point is that, while this result follows easily from our
 * methodology, this vulnerability was still considered novel 6 years
 * after the original re-entrancy attack to The Dao.
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
     *  Mint some new tokens.
     *
     *  @param  to      Target Address.
     *  @param  amount  The amount of newly minted tokens.
     *  @param  msg     The message value.
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
     * Get the balance of a given address.
     * This is an example of a Read-Only method.
     */
    method getBalance(addr: Address, msg: Msg, gas: nat) returns (g: nat, r: Try<uint256>)
        requires GInv() // ensures a sane context to read balances
        ensures r.Success? <==> gas >= 1
        ensures g == 0 || g <= gas - 1
        //ensures GInv()

        modifies {}
    {
        if !(gas >= 1) {
            return (if gas >= 1 then gas - 1 else 0), Revert();
        }
        g := gas - 1;
        r := Success(if addr in balances then balances[addr] else 0);
    }

    method transferROcall(from: Address, to: Address, amount: uint256, msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
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
        balances := balances[from := newAmount];

        //  If we swap the line above and the externalROCall, we cannot prove invariance of GInv()
        //  At this location GInv() must hold which puts a restriction on where external calls
        //  can occur.
        var g1, r1 := externalROCall(gas - 1);  // to.notify( from, amount );

        //  We can choose to propagate or not the failure of external call. Here choose not to.
        g, r := (if g1 >= 1 then g1 - 1 else 0), Success(());
    }

    /** Havoc a given type. */
    method {:extern} havoc<T>() returns (a: T)

    /**
     *  Simulate a potential re-entrant RO call.
     *  
     *  @param  gas The gas allocated to this call.
     *  @returns    The gas left after execution of the call and the status of the call.
     *
     */
     method externalROCall(gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        //ensures GInv()
        ensures g == 0 || g <= gas - 1
        modifies {}
        decreases gas
    {
        g := gas;
        //  Havoc `k` to introduce non-determinism.
        var k: nat := * ;
        //  Depending on the value of k % 2, re-entrant call or not or another external call.
        if k % 2 == 0 && g >= 1 {
            //  re-entrant call to getBalance.
            var from: GenericAccount := new GenericAccount();
            var to: GenericAccount := new GenericAccount();
            var amount: uint256 := *;
            var sender := new GenericAccount();
            var value := *;
            var msg := Msg(sender, value);
            var rTemp;
            g, rTemp := getBalance(from, msg, g - 1);
            r := *;
        }
        //  k % 2 == 1, no re-entrant call.
        //  Possible new external call
        var b:bool := *;
        if b && g >= 1 {
            //  external call makes an external call.
            g, r := externalROCall(g - 1);
        } else {
            //  external call does not make another external call.
            g := if gas >= 1 then gas - 1 else 0;
            r := *;
        }
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




