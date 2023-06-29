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
 * Provide non native types and if applicable, max/min values.
 */
module NonNativeTypes {

   /** 
    * The type `uint128` correspond to the restriction of the `int` type to
    * positive numbers that can be expressed in binary form with no more than 128
    * bits.
    * @note: 8 sections of 16 bits (16 bytes) 0x0000
    */
   newtype uint128 = i:nat | 0 <= i < 0x1_0000_0000_0000_0000_0000_0000_0000_0000
   const MAX_UINT128: nat := (0x1_0000_0000_0000_0000_0000_0000_0000_0000 as nat - 1) 

   /**
    * @note: 10 sections of 16 bits (20 bytes) 0x0000
    */
   newtype uint160 = i:nat | 0 <= i < 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
   const MAX_UINT160: nat := (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 as nat - 1) 

   /** 
    * The type `uint256` correspond to the restriction of the `int` type to
    * positive numbers that can be expressed in binary form with no more than 256
    * bits.
    * @note: 16 sections of 16 bits (32 bytes) 0x0000
    */
   newtype uint256 = i:nat | 0 <= i < 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000  //witness 0
   const MAX_UINT256 : nat := (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 as nat - 1) 

   type uint = uint256 

   type bytes32 = uint256
   
}