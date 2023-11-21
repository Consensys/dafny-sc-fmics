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

/** The Option type. */
datatype Option<T> = None() | Some(v: T) 

/** Environment to implement wrapper to get address.send */
datatype Try<T> = Success(v: T) | Revert()

/**  Decrement bounded by zero. */
function dec0(n: nat): nat { if n >= 1 then n - 1 else 0 }

/**
 *  The Simple Open Auction example.
 *
 *  @link{https://docs.soliditylang.org/en/develop/solidity-by-example.html}
 */

/** The type of the state of the contract. For verification only.  */
datatype State = State(
        ended: bool,
        highestBidder: Option<Address>, 
        pendingReturnsKeys: set<Address>, 
        highestBid: uint256)

/**
 *  The Simple Auction contract.
 *
 *  @note   The contract is intended to provide a Simple Open Auction.
 *          The auction has a beneficiary that should collect the highest bid at the end.
 *          Bidders can bid if their bid is higher than the current highest.
 *          The contract has a defined deadline for bidding. No bid should be allowed
 *          beyond that deadline. 
 *          Within now and `deadline`, bidders can bid, and overbid others or themselves.
 *          After the deadline, every bidder, except the winner, can withdraw their bids.
 *          The highest bid is transfered to the beneficiary.
 *  
 *  @note   In this contract, if you are currently the highest bid, you cannot withdraw.
 */
class SimpleAuctionRevertExternal extends Account {

    /** Beneficiary of the contract. */
    const beneficiary: Address
    /** Deadline in Unix time. */
    const auctionEndTime: uint256

    /** Accounts in the DB. 
     *  To prove properties with external calls, we need
     *  to include the set of references/adresses that are "reachable" from `this`.
     *  This is needed in Dafny to specify the frame.
     */
    const Repr: set<object>

    /** Current highest bidder ad highest bid. */ 
    var highestBidder: Option<Address>  
    /** Current highest bid. */
    var highestBid: uint256

    /** Bidders that were outbid, and how much this contract owe them. */
    var pendingReturns: map<Address, uint256>

    /** The auction can be ended only once and `ended` indicate whether it is completed. */
    var ended: bool 

    //  Verification variables
    ghost var otherbids: nat        // Sum of bids that have been overbid.
    ghost var withdrawals: nat      // Successful withdrawals

    /** `states` contains the history of the state variables of the contract,
    *       defined as the sequence of states reached after the  execution of a method/Tx.
    */
    ghost var states: seq<State>

    /** Contract invariant. */
    ghost predicate GInv()
        reads this
    {
        //  the contract object `this` and the beneficiary are different accounts.
        && this != beneficiary 
        //  A highestBid must have a highestBidder
        && (highestBid != 0 <==> highestBidder.Some?)  
        //  current balance of the contract.
        && (balance as nat >= (if !ended then highestBid as nat else 0) + otherbids - withdrawals)
        //  sum of values in pendingReturns
        && sum(pendingReturns) == otherbids - withdrawals
        //  the sequence of states reached so far satisfies:
        && |states| >= 1 
        && states[|states| - 1] == State(ended, highestBidder, pendingReturns.Keys, highestBid)
        //  when the contract has ended, the state of the contract is unchanged.
        && (forall i :: 0 <= i < |states| - 1 && states[i].ended ==> (states[i] == states[i + 1]))
        && this in Repr
        && beneficiary in Repr
    }

    /** Create an auction contract.
     *
     *  @param  biddingTime     The time period to bid from now, in seconds.
     *  @param  beneficiary_    The beneficiary of the contract.
     *  @param  block           The block this transaction is part of. Used to extract current time.
     *  @param  msg             The `msg` value for the caller of the ctor.
     *  @param  env             The set of addresses that external calls can originate from
     *                          or use.
     *
     *  @note       There is no current time in the network except as per the current
     *              block this transaction is included in.
     */
    constructor(biddingTime: uint256, beneficiary_: Address, block: Block, msg: Msg, env: set<object>)
        requires msg.value == 0 //  equivalent of not payable in Solidity.
        requires block.timestamp as nat + biddingTime as nat <= MAX_UINT256
        ensures ended == false && highestBid == 0 && highestBidder == None()
        //  this contract is newly allocated on the heap and cannot coincide with already accounts.
        ensures this != beneficiary_
        ensures Repr == {this, beneficiary} + env
        ensures GInv()
    {
        beneficiary := beneficiary_;
        auctionEndTime := block.timestamp + biddingTime;
        highestBidder := None();
        pendingReturns := map[];
        ended := false;
        highestBid := 0;
        Repr := {this, beneficiary} + env;
        //  ghost vars
        otherbids := 0;     //  no bids, so no overbids
        withdrawals := 0;   //  no withdrawals yet
        balance := 0;       //  initial balance of contract.
        // Initial state of the sequence `states`.
        states := [State(false, None(), {}, 0)];
    }   

    /**
     *  Provide a bidding method.
     *
     *  @param  msg     The context for the caller.
     */
    method bid(msg: Msg, block: Block, gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures r.Revert? <==> 
            !(
            // && msg.sender in otherAccounts
            && msg.sender != this
            && old(balance) as nat + msg.value as nat <= MAX_UINT256 as nat
            && msg.value > old(highestBid)
            && old(msg.sender.balance) >= msg.value
            && (if old(highestBidder) != None() && old(highestBidder.v) in old(pendingReturns) then var l := old(highestBidder.v); old(pendingReturns[l]) else 0) as nat + old(highestBid) as nat <= MAX_UINT256
            && !old(ended)
            && gas >= 2
            && block.timestamp  <= auctionEndTime
        )
        //  On revert, state is not modified.
        ensures |states| >= 2
        ensures r.Revert? ==> states[|states| - 1] == states[|states| - 2] 
        ensures r.Success? ==> old(balance) as nat + msg.value as nat <= MAX_UINT256 as nat
        // ensures r.Success? ==> balance >= old(balance) + msg.value //  balance in the contract increases. 
        ensures GInv()
        ensures g == 0 || g <= gas - 1   
        modifies this, msg.sender`balance
        decreases gas
    {
        if !(
            // && msg.sender in otherAccounts
            && msg.sender != this
            && balance as nat + msg.value as nat <= MAX_UINT256 as nat
            && msg.value > highestBid
            && msg.sender.balance >= msg.value
            && (if highestBidder != None() && highestBidder.v in pendingReturns then pendingReturns[highestBidder.v] else 0) as nat + highestBid as nat <= MAX_UINT256
            && !ended
            && gas >= 2
            && block.timestamp  <= auctionEndTime
        ) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return dec0(gas), Revert();
        }
        //  Process `msg` including ETH transfer before running the body of the method.
        g := processMsgValue(msg, gas - 1);
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];

        //  If there was a highest bidder, 
        if highestBid != 0 {
            mapAdd(pendingReturns, highestBidder.v, highestBid as nat);
            pendingReturns := pendingReturns[
                    highestBidder.v := 
                        (if  highestBidder.v in pendingReturns then pendingReturns[highestBidder.v] else 0) + 
                        highestBid];
            otherbids := otherbids + highestBid as nat;
        }
        highestBidder := Some(msg.sender);
        highestBid := msg.value;
        //  Append the new state.
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
        return dec0(g), Success(());
    }

    /**
     *  Bidders can withdraw at any time.
     *
     *  @param  msg     The context for the caller.
     *  @returns        Whether the refund was successful or not.
     */
    method withdraw(msg: Msg, gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures r.Revert? <==> 
            !(
                && msg.sender in old(pendingReturns) 
                && this != msg.sender
                && gas >= 2
            )
            || 
            (
                msg.sender in old(pendingReturns) 
                && old(msg.sender.balance) as nat + old(pendingReturns[msg.sender]) as nat > MAX_UINT256 as nat
            )
        ensures |states| >= 2
        ensures r.Revert? ==> states[|states| - 1] == states[|states| - 2]
        ensures GInv()
        ensures g == 0 || g <= gas - 1  

        modifies this, msg.sender`balance, Repr, beneficiary`balance
        decreases gas 
    {
        g := gas;
        if !(
            && msg.sender in pendingReturns 
            && this != msg.sender
            && gas >= 2
        ) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return dec0(gas), Revert();
        }
        if !(msg.sender.balance as nat + pendingReturns[msg.sender] as nat <= MAX_UINT256 as nat) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return dec0(gas), Revert();
        }
        var amount: uint := pendingReturns[msg.sender];
        if (amount > 0) {
            // It is important to set this to zero because the recipient
            // can call this function again as part of the receiving call
            // before `send` returns.
            mapSum(pendingReturns, msg.sender);
            assert this.balance >= amount; 

            mapResetKey(pendingReturns, msg.sender);
            pendingReturns := pendingReturns[msg.sender := 0];
            //  How can we be sure there is enough balance?
            withdrawals := withdrawals + amount as nat;
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            g := msg.sender.transfer(this, amount, gas - 1);
            //  Simulate other code after transfer
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            g, r := externalCall(dec0(g));
        }
        //  Append new state.
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
        return dec0(gas), Success(());
    }

    /**
     *  End the auction and send the highest bid to the beneficiary.
     *
     *  @param  msg     The caller's context.
     *  @param  block   The `block` context this transaction is part of.
     *  
     *  @note           Anyone can try to end the auction.
     */
    method auctionEnd(msg: Msg, block: Block, gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures r.Revert? <==> 
            !(
                && old(beneficiary.balance) as nat + old(highestBid) as nat <= MAX_UINT256
                && old(balance) >= old(highestBid)
                && block.timestamp < auctionEndTime
                && !old(ended)
                && gas >= 2 
            )
        ensures GInv()
        ensures g == 0 || g <= gas - 1  
        modifies this, beneficiary`balance, Repr
        ensures |states| >= 2
        ensures r.Revert? ==> states[|states| - 1] == states[|states| - 2]

        decreases gas
    {
        if !(
            && beneficiary.balance as nat + highestBid as nat <= MAX_UINT256
            && balance >= highestBid
            && block.timestamp < auctionEndTime
            && !ended
            && gas >= 2 
        ) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return dec0(gas), Revert();
        }
        ended := true;
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];    
        //     beneficiary.transfer(highestBid);
        g := beneficiary.transfer(this, highestBid, gas - 1);
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
        if g >= 1 {
            g, r := externalCall(g - 1); 
        }
        //  Append new state. 
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
        return dec0(g), Success(());
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
    // method externalCall(c: SimpleAuctionRevertExternal, gas: nat) returns (g: nat, r: Try<()>)
    method externalCall(gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures GInv()
        ensures g == 0 ||  g <= gas - 1 

        modifies this
        modifies Repr
        modifies beneficiary`balance
        decreases gas 
    {
        g := gas; 
        //  Havoc `k` to introduce non-determinism.
        var k: nat := havoc();
        //  Depending on the value of k % 3, re-entrant call or not or another external call.
        if k % 4 == 0 && g >= 1 {
            //  re-entrant call to bid.
            var b: Block := havoc();
            var msg: Msg := havocMsg();
            g, r := bid(msg, b, g - 1);
        } else if k % 4 == 1 && g >= 1 {
            //  re-entrant call to mint. 
            var b: Block := havoc();
            var msg: Msg := havocMsg();
            g, r := withdraw(msg, g - 1);
        } else if k % 4 == 2 && g >= 1 {
            //  re-entrant call to mint.  
            var b: Block := havoc();
            var msg: Msg := havocMsg();
            g, r := auctionEnd(msg, b, g - 1); 
        }
        //  Possible new external call
        var b:bool := havoc();
        if b && g >= 1 {
            //  external call makes an external call. 
            g, r := externalCall(g - 1); 
        } else {
            //  external call does not make another external call. 
            g := dec0(g);
            r := havoc();
        }
    }

    /** Havoc a given type. */
    method {:extern} havoc<T>() returns (a: T)

    method {:extern} havocMsg() returns (msg: Msg)
        ensures msg.sender in Repr

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
     *  Remove a number from a map value.
     *  
     *  @param  m   A map.
     *  @param  k   A key.
     *  @param  v   A value. 
     *
     *  If the value at key `k` is incremented by `v` then sum(m) is incremented by `v` too.
     */
    lemma mapResetKey(m: map<Address, uint256>, k: Address)
        requires k in m
        ensures sum(m[k := 0]) == sum(m) - m[k] as nat

    lemma mapSum(m: map<Address, uint256>, k: Address) 
        requires k in m 
        ensures sum(m) >= m[k] as nat

}



