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

/** The type of the state of the contract. Verification only.  */
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
class SimpleAuctionRevert extends Account {

    /** Beneficiary of the contract. */
    const beneficiary: Address
    /** Deadline in Unix time. */
    const auctionEndTime: uint256

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

    /** `states` if a sequence of states. 
     *  It contains the history of the state variables of the contract.
     *  `states` is defined as the sequence of states reached after the 
     *  execution of a method/Tx. 
     */
    ghost var states: seq<State>

    /**
     *  Contract invariant.
     */
    predicate GInv()
        reads this
    {
        //  the contract object `this` and the beneficiary are different accounts.
        && this != beneficiary 
        //  A highestBid must have a highestBidder
        && (highestBid != 0 <==> highestBidder.Some?)  
        //  current balance of the contract.
        && (balance as nat == (if !ended then highestBid as nat else 0) + otherbids - withdrawals)
        //  sum of values in pendingReturns
        && sum(pendingReturns) == otherbids - withdrawals
        //  the sequence of states reacghed so far satisfy:
        && |states| >= 1 
        && states[|states| - 1] == State(ended, highestBidder, pendingReturns.Keys, highestBid)
        //  when the contract has ended, the state of the contract is unchanged.
        && (forall i :: 0 <= i < |states| - 1 && states[i].ended ==> (states[i] == states[i + 1]))
    }

    /**
     *  Create an auction contract.
     *
     *  @param  biddingTime     The time period to bid from now, in seconds.
     *  @param  beneficiary_    The beneficiary of the contract.
     *  @param  block           The block this transaction is part of. Used to extract current time.
     *  @param  msg             The `msg` value for the caller of the ctor.
     *
     *  @note       There is no current time in the network except as per the current
     *              block this transaction is included in.
     */
    constructor(biddingTime: uint256, beneficiary_: Address, block: Block, msg: Msg)
        requires msg.value == 0 //  equivalent of not payable in Solidity.
        requires block.timestamp as nat + biddingTime as nat <= MAX_UINT256
        ensures ended == false && highestBid == 0 && highestBidder == None()
        //  this contract is newly allocated on the heap and cannot coincide with already accounts.
        ensures this != beneficiary_
        ensures GInv()
    {
        beneficiary := beneficiary_;
        auctionEndTime := block.timestamp + biddingTime;
        highestBidder := None();
        pendingReturns := map[];
        ended := false;
        highestBid := 0;
        //  ghost vars
        otherbids := 0;     //  no bid so no bid can be overbid.
        withdrawals := 0;   //  no withdrawals yet
        balance := 0;       //  initial balance of contract.
        // Initial state of the sequence `states`.
        states := [State(false, None(), {}, 0)];
    }   

    /**
     *  Provide a bidding method.
     *
     *  @param  msg     The context for the caller.
     *  @param  block   The `block` context this transaction is part of.
     */
    method bid(msg: Msg, block: Block, gas: nat) returns (g: nat, r: Try<()>)
        requires GInv()
        ensures states == old(states) + [State(ended, highestBidder, pendingReturns.Keys, highestBid)]
        ensures r.Revert? <==> 
            !(
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
        ensures r.Revert? ==> states[|states| - 1] == states[|states| - 2]
        ensures r.Success? ==> old(balance) as nat + msg.value as nat <= MAX_UINT256 as nat
        ensures r.Success? ==> balance >= old(balance) + msg.value //  balance in the contract increases. 
        ensures GInv()
    
        modifies this, msg.sender`balance
    {
        if !(
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
        //  Process `msg` including ETH trabsfer before running the body of the method.
        g := processMsgValue(msg, gas - 1);
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
     *  @param  block   The `block` context this transaction is part of.
     *  @returns        Whether the refund was successful or not.
     */
    method withdraw(msg: Msg, block: Block, gas: nat) returns (g: nat, r: Try<()>)
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
        ensures states == old(states) + [State(ended, highestBidder, pendingReturns.Keys, highestBid)]
        ensures GInv()

        modifies this, msg.sender`balance
    {
        g := gas;
        if !(
            && msg.sender in pendingReturns 
            && this != msg.sender
            && gas >= 2
        ) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return if g >= 1 then g - 1 else 0, Revert();
        }
        if !(msg.sender.balance as nat + pendingReturns[msg.sender] as nat <= MAX_UINT256 as nat) {
            states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return if g >= 1 then g - 1 else 0, Revert();
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
            g := msg.sender.transfer(this, amount, gas - 1);
            withdrawals := withdrawals + amount as nat;
        }
        //  Append new state.
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
        return dec0(g), Success(());
    }

    /**
     *
     *  @param  msg     The context for the caller.
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

        ensures r.Success? ==> ended
        ensures highestBid == old(highestBid)
        ensures r.Success? ==> beneficiary.balance >= old(beneficiary.balance) + highestBid 
        ensures states == old(states) + [State(ended, highestBidder, pendingReturns.Keys, highestBid)]
        ensures GInv()
        modifies this, beneficiary`balance
    {
        if !(
            && beneficiary.balance as nat + highestBid as nat <= MAX_UINT256
            && balance >= highestBid
            && block.timestamp < auctionEndTime
            && !ended
            && gas >= 2 
        ) {
            states := old(states) + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];
            return dec0(gas), Revert();
        }
        ended := true;
        //     beneficiary.transfer(highestBid);
        g := beneficiary.transfer(this, highestBid, gas - 1);
        //  Append new state. 
        states := states + [State(ended, highestBidder, pendingReturns.Keys, highestBid)];    
        return dec0(g), Success(());
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



