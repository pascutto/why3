(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Printer for extracted Evm code *)

open Compile
open Ident
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Pdecl
open Printer

type info = {
  info_syn          : syntax_map;
  info_literal      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
  info_flat         : bool;
  info_current_ph   : string list; (* current path *)
}

let debug =
  Debug.register_info_flag ~desc:"EVM extraction" "evm_extraction"
let gas_checking =
  Debug.register_flag ~desc:"EVM gas checking" "evm_gas_checking"

module EVM = struct

  type instruction =
   | STOP
   | ADD
   | SUB
   | MUL
   | DIV
   | SDIV
   | MOD
   | SMOD
   | EXP
   | NOT
   | LT
   | GT
   | SLT
   | SGT
   | EQ
   | ISZERO
   | AND
   | OR
   | XOR
   | BYTE
   | SHL
   | SHR
   | SAR
   | ADDMOD
   | MULMOD
   | SIGNEXTEND
   | KECCAK256
   | ADDRESS
   | BALANCE
   | ORIGIN
   | CALLER
   | CALLVALUE
   | CALLDATALOAD
   | CALLDATASIZE
   | CALLDATACOPY
   | CODESIZE
   | CODECOPY
   | GASPRICE
   | EXTCODESIZE
   | EXTCODECOPY
   | RETURNDATASIZE
   | RETURNDATACOPY
   | EXTCODEHASH
   | BLOCKHASH
   | COINBASE
   | TIMESTAMP
   | NUMBER
   | DIFFICULTY
   | GASLIMIT
   | POP
   | MLOAD
   | MSTORE
   | MSTORE8
   | SLOAD
   | SSTORE
   | JUMP
   | JUMPI
   | PC
   | MSIZE
   | GAS
   | JUMPDEST
   | PUSH1 of BigInt.t
   | PUSH2 of BigInt.t
   | PUSH3 of BigInt.t
   | PUSH4 of BigInt.t
   | PUSH5 of BigInt.t
   | PUSH6 of BigInt.t
   | PUSH7 of BigInt.t
   | PUSH8 of BigInt.t
   | PUSH9 of BigInt.t
   | PUSH10 of BigInt.t
   | PUSH11 of BigInt.t
   | PUSH12 of BigInt.t
   | PUSH13 of BigInt.t
   | PUSH14 of BigInt.t
   | PUSH15 of BigInt.t
   | PUSH16 of BigInt.t
   | PUSH17 of BigInt.t
   | PUSH18 of BigInt.t
   | PUSH19 of BigInt.t
   | PUSH20 of BigInt.t
   | PUSH21 of BigInt.t
   | PUSH22 of BigInt.t
   | PUSH23 of BigInt.t
   | PUSH24 of BigInt.t
   | PUSH25 of BigInt.t
   | PUSH26 of BigInt.t
   | PUSH27 of BigInt.t
   | PUSH28 of BigInt.t
   | PUSH29 of BigInt.t
   | PUSH30 of BigInt.t
   | PUSH31 of BigInt.t
   | PUSH32 of BigInt.t
   | DUP1
   | DUP2
   | DUP3
   | DUP4
   | DUP5
   | DUP6
   | DUP7
   | DUP8
   | DUP9
   | DUP10
   | DUP11
   | DUP12
   | DUP13
   | DUP14
   | DUP15
   | DUP16
   | SWAP1
   | SWAP2
   | SWAP3
   | SWAP4
   | SWAP5
   | SWAP6
   | SWAP7
   | SWAP8
   | SWAP9
   | SWAP10
   | SWAP11
   | SWAP12
   | SWAP13
   | SWAP14
   | SWAP15
   | SWAP16
   | LOG0
   | LOG1
   | LOG2
   | LOG3
   | LOG4
   | CREATE
   | CALL
   | CALLCODE
   | RETURN
   | DELEGATECALL
   | STATICCALL
   | CREATE2
   | REVERT
   | INVALID
   | SELFDESTRUCT

  let equal a b =
    match a,b with
    | STOP, STOP -> true
    | ADD, ADD -> true
    | SUB, SUB -> true
    | MUL, MUL -> true
    | DIV, DIV -> true
    | SDIV, SDIV -> true
    | MOD, MOD -> true
    | SMOD, SMOD -> true
    | EXP, EXP -> true
    | NOT, NOT -> true
    | LT, LT -> true
    | GT, GT -> true
    | SLT, SLT -> true
    | SGT, SGT -> true
    | EQ, EQ -> true
    | ISZERO, ISZERO -> true
    | AND, AND -> true
    | OR, OR -> true
    | XOR, XOR -> true
    | BYTE, BYTE -> true
    | SHL, SHL -> true
    | SHR, SHR -> true
    | SAR, SAR -> true
    | ADDMOD, ADDMOD -> true
    | MULMOD, MULMOD -> true
    | SIGNEXTEND, SIGNEXTEND -> true
    | KECCAK256, KECCAK256 -> true
    | ADDRESS, ADDRESS -> true
    | BALANCE, BALANCE -> true
    | ORIGIN, ORIGIN -> true
    | CALLER, CALLER -> true
    | CALLVALUE, CALLVALUE -> true
    | CALLDATALOAD, CALLDATALOAD -> true
    | CALLDATASIZE, CALLDATASIZE -> true
    | CALLDATACOPY, CALLDATACOPY -> true
    | CODESIZE, CODESIZE -> true
    | CODECOPY, CODECOPY -> true
    | GASPRICE, GASPRICE -> true
    | EXTCODESIZE, EXTCODESIZE -> true
    | EXTCODECOPY, EXTCODECOPY -> true
    | RETURNDATASIZE, RETURNDATASIZE -> true
    | RETURNDATACOPY, RETURNDATACOPY -> true
    | EXTCODEHASH, EXTCODEHASH -> true
    | BLOCKHASH, BLOCKHASH -> true
    | COINBASE, COINBASE -> true
    | TIMESTAMP, TIMESTAMP -> true
    | NUMBER, NUMBER -> true
    | DIFFICULTY, DIFFICULTY -> true
    | GASLIMIT, GASLIMIT -> true
    | POP, POP -> true
    | MLOAD, MLOAD -> true
    | MSTORE, MSTORE -> true
    | MSTORE8, MSTORE8 -> true
    | SLOAD, SLOAD -> true
    | SSTORE, SSTORE -> true
    | JUMPDEST, JUMPDEST -> true
    | JUMP, JUMP -> true
    | JUMPI, JUMPI -> true
    | PC, PC -> true
    | MSIZE, MSIZE -> true
    | GAS, GAS -> true
    | PUSH1 x, PUSH1 y -> BigInt.compare x y = 0
    | PUSH2 x, PUSH2 y -> BigInt.compare x y = 0
    | PUSH3 x, PUSH3 y -> BigInt.compare x y = 0
    | PUSH4 x, PUSH4 y -> BigInt.compare x y = 0
    | PUSH5 x, PUSH5 y -> BigInt.compare x y = 0
    | PUSH6 x, PUSH6 y -> BigInt.compare x y = 0
    | PUSH7 x, PUSH7 y -> BigInt.compare x y = 0
    | PUSH8 x, PUSH8 y -> BigInt.compare x y = 0
    | PUSH9 x, PUSH9 y -> BigInt.compare x y = 0
    | PUSH10 x, PUSH10 y -> BigInt.compare x y = 0
    | PUSH11 x, PUSH11 y -> BigInt.compare x y = 0
    | PUSH12 x, PUSH12 y -> BigInt.compare x y = 0
    | PUSH13 x, PUSH13 y -> BigInt.compare x y = 0
    | PUSH14 x, PUSH14 y -> BigInt.compare x y = 0
    | PUSH15 x, PUSH15 y -> BigInt.compare x y = 0
    | PUSH16 x, PUSH16 y -> BigInt.compare x y = 0
    | PUSH17 x, PUSH17 y -> BigInt.compare x y = 0
    | PUSH18 x, PUSH18 y -> BigInt.compare x y = 0
    | PUSH19 x, PUSH19 y -> BigInt.compare x y = 0
    | PUSH20 x, PUSH20 y -> BigInt.compare x y = 0
    | PUSH21 x, PUSH21 y -> BigInt.compare x y = 0
    | PUSH22 x, PUSH22 y -> BigInt.compare x y = 0
    | PUSH23 x, PUSH23 y -> BigInt.compare x y = 0
    | PUSH24 x, PUSH24 y -> BigInt.compare x y = 0
    | PUSH25 x, PUSH25 y -> BigInt.compare x y = 0
    | PUSH26 x, PUSH26 y -> BigInt.compare x y = 0
    | PUSH27 x, PUSH27 y -> BigInt.compare x y = 0
    | PUSH28 x, PUSH28 y -> BigInt.compare x y = 0
    | PUSH29 x, PUSH29 y -> BigInt.compare x y = 0
    | PUSH30 x, PUSH30 y -> BigInt.compare x y = 0
    | PUSH31 x, PUSH31 y -> BigInt.compare x y = 0
    | PUSH32 x, PUSH32 y -> BigInt.compare x y = 0
    | DUP1, DUP1 -> true
    | DUP2, DUP2 -> true
    | DUP3, DUP3 -> true
    | DUP4, DUP4 -> true
    | DUP5, DUP5 -> true
    | DUP6, DUP6 -> true
    | DUP7, DUP7 -> true
    | DUP8, DUP8 -> true
    | DUP9, DUP9 -> true
    | DUP10, DUP10 -> true
    | DUP11, DUP11 -> true
    | DUP12, DUP12 -> true
    | DUP13, DUP13 -> true
    | DUP14, DUP14 -> true
    | DUP15, DUP15 -> true
    | DUP16, DUP16 -> true
    | SWAP1, SWAP1 -> true
    | SWAP2, SWAP2 -> true
    | SWAP3, SWAP3 -> true
    | SWAP4, SWAP4 -> true
    | SWAP5, SWAP5 -> true
    | SWAP6, SWAP6 -> true
    | SWAP7, SWAP7 -> true
    | SWAP8, SWAP8 -> true
    | SWAP9, SWAP9 -> true
    | SWAP10, SWAP10 -> true
    | SWAP11, SWAP11 -> true
    | SWAP12, SWAP12 -> true
    | SWAP13, SWAP13 -> true
    | SWAP14, SWAP14 -> true
    | SWAP15, SWAP15 -> true
    | SWAP16, SWAP16 -> true
    | LOG0, LOG0 -> true
    | LOG1, LOG1 -> true
    | LOG2, LOG2 -> true
    | LOG3, LOG3 -> true
    | LOG4, LOG4 -> true
    | CREATE, CREATE -> true
    | CALL, CALL -> true
    | CALLCODE, CALLCODE -> true
    | RETURN, RETURN -> true
    | DELEGATECALL, DELEGATECALL -> true
    | STATICCALL, STATICCALL -> true
    | CREATE2, CREATE2 -> true
    | REVERT, REVERT -> true
    | INVALID, INVALID -> true
    | SELFDESTRUCT, SELFDESTRUCT -> true
    | _ -> false

type price =
  | PriceZero
  | PriceVeryLow
  | PriceLow
  | PriceMid
  | PriceHigh
  | PriceSpecial
  | PriceSpecialOver of int (** overapproximation of the cost *)
  | PriceBase
  | PriceExtCode
  | PriceExt
  | PriceBalance


let price_cost price =
  let p = match price with
  | PriceZero -> 0
  | PriceVeryLow -> 3
  | PriceLow -> 5
  | PriceMid -> 8
  | PriceHigh -> 10
  | PriceSpecial -> invalid_arg "PriceSpecial"
  | PriceSpecialOver i -> i
  | PriceBase -> 2
  | PriceExtCode -> 700
  | PriceExt -> 20
  | PriceBalance -> 400
  in
  BigInt.of_int p



type info =
  {
    name: string;
    pushed: int;
    args: int;
    ret: int;
    sideeffects: bool;
    price: price;
    code: int;
  }

let get_info = function
  | STOP -> { name = "STOP"; pushed = 0; args = 0; ret = 0; sideeffects = true; price = PriceZero; code = 0x00; }
  | ADD -> { name = "ADD"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x01; }
  | SUB -> { name = "SUB"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x03; }
  | MUL -> { name = "MUL"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x02; }
  | DIV -> { name = "DIV"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x04; }
  | SDIV -> { name = "SDIV"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x05; }
  | MOD -> { name = "MOD"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x06; }
  | SMOD -> { name = "SMOD"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x07; }
  | EXP -> { name = "EXP"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceSpecial; code = 0x0a; }
  | NOT -> { name = "NOT"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x19; }
  | LT -> { name =  "LT"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x10; }
  | GT -> { name =  "GT"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x11; }
  | SLT -> { name = "SLT"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x12; }
  | SGT -> { name = "SGT"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x13; }
  | EQ -> { name =  "EQ"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x14; }
  | ISZERO -> { name = "ISZERO"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x15; }
  | AND -> { name = "AND"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x16; }
  | OR -> { name =  "OR"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x17; }
  | XOR -> { name = "XOR"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x18; }
  | BYTE -> { name = "BYTE"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x1a; }
  | SHL -> { name = "SHL"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x1b; }
  | SHR -> { name = "SHR"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x1c; }
  | SAR -> { name = "SAR"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x1d; }
  | ADDMOD -> { name = "ADDMOD"; pushed = 0; args = 3; ret = 1; sideeffects = false; price = PriceMid; code = 0x08; }
  | MULMOD -> { name = "MULMOD"; pushed = 0; args = 3; ret = 1; sideeffects = false; price = PriceMid; code = 0x09; }
  | SIGNEXTEND -> { name = "SIGNEXTEND"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x0b; }
  | KECCAK256 -> { name = "KECCAK256"; pushed = 0; args = 2; ret = 1; sideeffects = true; price = PriceSpecial; code = 0x20; }
  | ADDRESS -> { name = "ADDRESS"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x30; }
  | BALANCE -> { name = "BALANCE"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceBalance; code = 0x31; }
  | ORIGIN -> { name = "ORIGIN"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x32; }
  | CALLER -> { name = "CALLER"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x33; }
  | CALLVALUE -> { name = "CALLVALUE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x34; }
  | CALLDATALOAD -> { name = "CALLDATALOAD"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x35; }
  | CALLDATASIZE -> { name = "CALLDATASIZE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x36; }
  | CALLDATACOPY -> { name = "CALLDATACOPY"; pushed = 0; args = 3; ret = 0; sideeffects = true; price = PriceVeryLow; code = 0x37; }
  | CODESIZE -> { name = "CODESIZE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x38; }
  | CODECOPY -> { name = "CODECOPY"; pushed = 0; args = 3; ret = 0; sideeffects = true; price = PriceVeryLow; code = 0x39; }
  | GASPRICE -> { name = "GASPRICE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x3a; }
  | EXTCODESIZE -> { name = "EXTCODESIZE"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceExtCode; code = 0x3b; }
  | EXTCODECOPY -> { name = "EXTCODECOPY"; pushed = 0; args = 4; ret = 0; sideeffects = true; price = PriceExtCode; code = 0x3c; }
  | RETURNDATASIZE -> { name = "RETURNDATASIZE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x3d; }
  | RETURNDATACOPY -> { name = "RETURNDATACOPY"; pushed = 0; args = 3; ret = 0; sideeffects = true; price = PriceVeryLow; code = 0x3e; }
  | EXTCODEHASH -> { name = "EXTCODEHASH"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceBalance; code = 0x3f; }
  | BLOCKHASH -> { name = "BLOCKHASH"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceExt; code = 0x40; }
  | COINBASE -> { name = "COINBASE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x41; }
  | TIMESTAMP -> { name = "TIMESTAMP"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x42; }
  | NUMBER -> { name = "NUMBER"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x43; }
  | DIFFICULTY -> { name = "DIFFICULTY"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x44; }
  | GASLIMIT -> { name = "GASLIMIT"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x45; }
  | POP -> { name = "POP"; pushed = 0; args = 1; ret = 0; sideeffects = false; price = PriceBase; code = 0x50; }
  | MLOAD -> { name = "MLOAD"; pushed = 0; args = 1; ret = 1; sideeffects = true; price = PriceVeryLow; code = 0x51; }
  | MSTORE -> { name = "MSTORE"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceVeryLow; code = 0x52; }
  | MSTORE8 -> { name = "MSTORE8"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceVeryLow; code = 0x53; }
  | SLOAD -> { name = "SLOAD"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceSpecialOver(200); code = 0x54; }
  | SSTORE -> { name = "SSTORE"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceSpecialOver(20000); code = 0x55; }
  | JUMP -> { name = "JUMP"; pushed = 0; args = 1; ret = 0; sideeffects = true; price = PriceMid; code = 0x56; }
  | JUMPI -> { name = "JUMPI"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceHigh; code = 0x57; }
  | PC -> { name =  "PC"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x58; }
  | MSIZE -> { name = "MSIZE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x59; }
  | GAS -> { name = "GAS"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x5a; }
  | JUMPDEST -> { name = "JUMPDEST"; pushed = 0; args = 0; ret = 0; sideeffects = true; price = PriceSpecialOver(1); code = 0x5b; }
  | PUSH1 _ -> { name = "PUSH1"; pushed = 1; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x60; }
  | PUSH2 _ -> { name = "PUSH2"; pushed = 2; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x61; }
  | PUSH3 _ -> { name = "PUSH3"; pushed = 3; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x62; }
  | PUSH4 _ -> { name = "PUSH4"; pushed = 4; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x63; }
  | PUSH5 _ -> { name = "PUSH5"; pushed = 5; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x64; }
  | PUSH6 _ -> { name = "PUSH6"; pushed = 6; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x65; }
  | PUSH7 _ -> { name = "PUSH7"; pushed = 7; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x66; }
  | PUSH8 _ -> { name = "PUSH8"; pushed = 8; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x67; }
  | PUSH9 _ -> { name = "PUSH9"; pushed = 9; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x68; }
  | PUSH10 _ -> { name = "PUSH10"; pushed = 10; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x69; }
  | PUSH11 _ -> { name = "PUSH11"; pushed = 11; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6a; }
  | PUSH12 _ -> { name = "PUSH12"; pushed = 12; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6b; }
  | PUSH13 _ -> { name = "PUSH13"; pushed = 13; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6c; }
  | PUSH14 _ -> { name = "PUSH14"; pushed = 14; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6d; }
  | PUSH15 _ -> { name = "PUSH15"; pushed = 15; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6e; }
  | PUSH16 _ -> { name = "PUSH16"; pushed = 16; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x6f; }
  | PUSH17 _ -> { name = "PUSH17"; pushed = 17; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x70; }
  | PUSH18 _ -> { name = "PUSH18"; pushed = 18; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x71; }
  | PUSH19 _ -> { name = "PUSH19"; pushed = 19; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x72; }
  | PUSH20 _ -> { name = "PUSH20"; pushed = 20; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x73; }
  | PUSH21 _ -> { name = "PUSH21"; pushed = 21; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x74; }
  | PUSH22 _ -> { name = "PUSH22"; pushed = 22; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x75; }
  | PUSH23 _ -> { name = "PUSH23"; pushed = 23; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x76; }
  | PUSH24 _ -> { name = "PUSH24"; pushed = 24; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x77; }
  | PUSH25 _ -> { name = "PUSH25"; pushed = 25; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x78; }
  | PUSH26 _ -> { name = "PUSH26"; pushed = 26; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x79; }
  | PUSH27 _ -> { name = "PUSH27"; pushed = 27; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7a; }
  | PUSH28 _ -> { name = "PUSH28"; pushed = 28; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7b; }
  | PUSH29 _ -> { name = "PUSH29"; pushed = 29; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7c; }
  | PUSH30 _ -> { name = "PUSH30"; pushed = 30; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7d; }
  | PUSH31 _ -> { name = "PUSH31"; pushed = 31; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7e; }
  | PUSH32 _ -> { name = "PUSH32"; pushed = 32; args = 0; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x7f; }
  | DUP1 -> { name = "DUP1"; pushed = 0; args = 1; ret = 2; sideeffects = false; price = PriceVeryLow; code = 0x80; }
  | DUP2 -> { name = "DUP2"; pushed = 0; args = 2; ret = 3; sideeffects = false; price = PriceVeryLow; code = 0x81; }
  | DUP3 -> { name = "DUP3"; pushed = 0; args = 3; ret = 4; sideeffects = false; price = PriceVeryLow; code = 0x82; }
  | DUP4 -> { name = "DUP4"; pushed = 0; args = 4; ret = 5; sideeffects = false; price = PriceVeryLow; code = 0x83; }
  | DUP5 -> { name = "DUP5"; pushed = 0; args = 5; ret = 6; sideeffects = false; price = PriceVeryLow; code = 0x84; }
  | DUP6 -> { name = "DUP6"; pushed = 0; args = 6; ret = 7; sideeffects = false; price = PriceVeryLow; code = 0x85; }
  | DUP7 -> { name = "DUP7"; pushed = 0; args = 7; ret = 8; sideeffects = false; price = PriceVeryLow; code = 0x86; }
  | DUP8 -> { name = "DUP8"; pushed = 0; args = 8; ret = 9; sideeffects = false; price = PriceVeryLow; code = 0x87; }
  | DUP9 -> { name = "DUP9"; pushed = 0; args = 9; ret = 10; sideeffects = false; price = PriceVeryLow; code = 0x88; }
  | DUP10 -> { name = "DUP10"; pushed = 0; args = 10; ret = 11; sideeffects = false; price = PriceVeryLow; code = 0x89; }
  | DUP11 -> { name = "DUP11"; pushed = 0; args = 11; ret = 12; sideeffects = false; price = PriceVeryLow; code = 0x8a; }
  | DUP12 -> { name = "DUP12"; pushed = 0; args = 12; ret = 13; sideeffects = false; price = PriceVeryLow; code = 0x8b; }
  | DUP13 -> { name = "DUP13"; pushed = 0; args = 13; ret = 14; sideeffects = false; price = PriceVeryLow; code = 0x8c; }
  | DUP14 -> { name = "DUP14"; pushed = 0; args = 14; ret = 15; sideeffects = false; price = PriceVeryLow; code = 0x8d; }
  | DUP15 -> { name = "DUP15"; pushed = 0; args = 15; ret = 16; sideeffects = false; price = PriceVeryLow; code = 0x8e; }
  | DUP16 -> { name = "DUP16"; pushed = 0; args = 16; ret = 17; sideeffects = false; price = PriceVeryLow; code = 0x8f; }
  | SWAP1 -> { name = "SWAP1"; pushed = 0; args = 2; ret = 2; sideeffects = false; price = PriceVeryLow; code = 0x90; }
  | SWAP2 -> { name = "SWAP2"; pushed = 0; args = 3; ret = 3; sideeffects = false; price = PriceVeryLow; code = 0x91; }
  | SWAP3 -> { name = "SWAP3"; pushed = 0; args = 4; ret = 4; sideeffects = false; price = PriceVeryLow; code = 0x92; }
  | SWAP4 -> { name = "SWAP4"; pushed = 0; args = 5; ret = 5; sideeffects = false; price = PriceVeryLow; code = 0x93; }
  | SWAP5 -> { name = "SWAP5"; pushed = 0; args = 6; ret = 6; sideeffects = false; price = PriceVeryLow; code = 0x94; }
  | SWAP6 -> { name = "SWAP6"; pushed = 0; args = 7; ret = 7; sideeffects = false; price = PriceVeryLow; code = 0x95; }
  | SWAP7 -> { name = "SWAP7"; pushed = 0; args = 8; ret = 8; sideeffects = false; price = PriceVeryLow; code = 0x96; }
  | SWAP8 -> { name = "SWAP8"; pushed = 0; args = 9; ret = 9; sideeffects = false; price = PriceVeryLow; code = 0x97; }
  | SWAP9 -> { name = "SWAP9"; pushed = 0; args = 10; ret = 10; sideeffects = false; price = PriceVeryLow; code = 0x98; }
  | SWAP10 -> { name = "SWAP10"; pushed = 0; args = 11; ret = 11; sideeffects = false; price = PriceVeryLow; code = 0x99; }
  | SWAP11 -> { name = "SWAP11"; pushed = 0; args = 12; ret = 12; sideeffects = false; price = PriceVeryLow; code = 0x9a; }
  | SWAP12 -> { name = "SWAP12"; pushed = 0; args = 13; ret = 13; sideeffects = false; price = PriceVeryLow; code = 0x9b; }
  | SWAP13 -> { name = "SWAP13"; pushed = 0; args = 14; ret = 14; sideeffects = false; price = PriceVeryLow; code = 0x9c; }
  | SWAP14 -> { name = "SWAP14"; pushed = 0; args = 15; ret = 15; sideeffects = false; price = PriceVeryLow; code = 0x9d; }
  | SWAP15 -> { name = "SWAP15"; pushed = 0; args = 16; ret = 16; sideeffects = false; price = PriceVeryLow; code = 0x9e; }
  | SWAP16 -> { name = "SWAP16"; pushed = 0; args = 17; ret = 17; sideeffects = false; price = PriceVeryLow; code = 0x9f; }
  | LOG0 -> { name = "LOG0"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xa0; }
  | LOG1 -> { name = "LOG1"; pushed = 0; args = 3; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xa1; }
  | LOG2 -> { name = "LOG2"; pushed = 0; args = 4; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xa2; }
  | LOG3 -> { name = "LOG3"; pushed = 0; args = 5; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xa3; }
  | LOG4 -> { name = "LOG4"; pushed = 0; args = 6; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xa4; }
  | CREATE -> { name = "CREATE"; pushed = 0; args = 3; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xf0; }
  | CALL -> { name = "CALL"; pushed = 0; args = 7; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xf1; }
  | CALLCODE -> { name = "CALLCODE"; pushed = 0; args = 7; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xf2; }
  | RETURN -> { name = "RETURN"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceZero; code = 0xf3; }
  | DELEGATECALL -> { name = "DELEGATECALL"; pushed = 0; args = 6; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xf4; }
  | STATICCALL -> { name = "STATICCALL"; pushed = 0; args = 6; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xfa; }
  | CREATE2 -> { name = "CREATE2"; pushed = 0; args = 4; ret = 1; sideeffects = true; price = PriceSpecial; code = 0xfe; }
  | REVERT -> { name = "REVERT"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceZero; code = 0xfd; }
  | INVALID -> { name = "INVALID"; pushed = 0; args = 0; ret = 0; sideeffects = true; price = PriceZero; code = 0xfe; }
  | SELFDESTRUCT -> { name = "SELFDESTRUCT"; pushed = 0; args = 1; ret = 0; sideeffects = true; price = PriceSpecial; code = 0xff; }

let size instr =
  1 + (get_info instr).pushed

let sizel l =
  List.fold_left (fun acc e -> acc + (size e)) 0 l

let cost instr =
  price_cost  (get_info instr).price

let costl l =
  List.fold_left (fun acc e -> BigInt.add acc (cost e)) BigInt.zero l

let pp_binary buf = function
   | STOP
   | ADD
   | SUB
   | MUL
   | DIV
   | SDIV
   | MOD
   | SMOD
   | EXP
   | NOT
   | LT
   | GT
   | SLT
   | SGT
   | EQ
   | ISZERO
   | AND
   | OR
   | XOR
   | BYTE
   | SHL
   | SHR
   | SAR
   | ADDMOD
   | MULMOD
   | SIGNEXTEND
   | KECCAK256
   | ADDRESS
   | BALANCE
   | ORIGIN
   | CALLER
   | CALLVALUE
   | CALLDATALOAD
   | CALLDATASIZE
   | CALLDATACOPY
   | CODESIZE
   | CODECOPY
   | GASPRICE
   | EXTCODESIZE
   | EXTCODECOPY
   | RETURNDATASIZE
   | RETURNDATACOPY
   | EXTCODEHASH
   | BLOCKHASH
   | COINBASE
   | TIMESTAMP
   | NUMBER
   | DIFFICULTY
   | GASLIMIT
   | POP
   | MLOAD
   | MSTORE
   | MSTORE8
   | SLOAD
   | SSTORE
   | JUMP
   | JUMPI
   | PC
   | MSIZE
   | GAS
   | JUMPDEST
   | DUP1
   | DUP2
   | DUP3
   | DUP4
   | DUP5
   | DUP6
   | DUP7
   | DUP8
   | DUP9
   | DUP10
   | DUP11
   | DUP12
   | DUP13
   | DUP14
   | DUP15
   | DUP16
   | SWAP1
   | SWAP2
   | SWAP3
   | SWAP4
   | SWAP5
   | SWAP6
   | SWAP7
   | SWAP8
   | SWAP9
   | SWAP10
   | SWAP11
   | SWAP12
   | SWAP13
   | SWAP14
   | SWAP15
   | SWAP16
   | LOG0
   | LOG1
   | LOG2
   | LOG3
   | LOG4
   | CREATE
   | CALL
   | CALLCODE
   | RETURN
   | DELEGATECALL
   | STATICCALL
   | CREATE2
   | REVERT
   | INVALID
   | SELFDESTRUCT as op ->
       Buffer.add_char buf (Char.chr (get_info op).code)
   | PUSH1 i
   | PUSH2 i
   | PUSH3 i
   | PUSH4 i
   | PUSH5 i
   | PUSH6 i
   | PUSH7 i
   | PUSH8 i
   | PUSH9 i
   | PUSH10 i
   | PUSH11 i
   | PUSH12 i
   | PUSH13 i
   | PUSH14 i
   | PUSH15 i
   | PUSH16 i
   | PUSH17 i
   | PUSH18 i
   | PUSH19 i
   | PUSH20 i
   | PUSH21 i
   | PUSH22 i
   | PUSH23 i
   | PUSH24 i
   | PUSH25 i
   | PUSH26 i
   | PUSH27 i
   | PUSH28 i
   | PUSH29 i
   | PUSH30 i
   | PUSH31 i
   | PUSH32 i as op ->
       let i = ref i in
       let _256 = BigInt.of_int 256 in
       let s = Bytes.make ((get_info op).pushed + 1) '-' in
       Bytes.set s 0 (Char.chr (get_info op).code);
       for j=(get_info op).pushed downto 1 do
         let d,m = BigInt.euclidean_div_mod !i _256 in
         i := d;
         Bytes.set s j (Char.chr (BigInt.to_int m));
       done;
       Buffer.add_bytes buf s

let string_hex n =
  assert (0 <= n && n < 256);
  Printf.sprintf "%02x" n

let _256 = BigInt.of_int 256
let rec print_int_hex size d acc =
  if size < 1 then acc
  else
    let d,m = BigInt.euclidean_div_mod d _256 in
    let s = string_hex (BigInt.to_int m) in
    print_int_hex (size-1) d (s^acc)

let print_int_hex size d = print_int_hex size d ""

let pp_ascii buf = function
   | STOP
   | ADD
   | SUB
   | MUL
   | DIV
   | SDIV
   | MOD
   | SMOD
   | EXP
   | NOT
   | LT
   | GT
   | SLT
   | SGT
   | EQ
   | ISZERO
   | AND
   | OR
   | XOR
   | BYTE
   | SHL
   | SHR
   | SAR
   | ADDMOD
   | MULMOD
   | SIGNEXTEND
   | KECCAK256
   | ADDRESS
   | BALANCE
   | ORIGIN
   | CALLER
   | CALLVALUE
   | CALLDATALOAD
   | CALLDATASIZE
   | CALLDATACOPY
   | CODESIZE
   | CODECOPY
   | GASPRICE
   | EXTCODESIZE
   | EXTCODECOPY
   | RETURNDATASIZE
   | RETURNDATACOPY
   | EXTCODEHASH
   | BLOCKHASH
   | COINBASE
   | TIMESTAMP
   | NUMBER
   | DIFFICULTY
   | GASLIMIT
   | POP
   | MLOAD
   | MSTORE
   | MSTORE8
   | SLOAD
   | SSTORE
   | JUMP
   | JUMPI
   | PC
   | MSIZE
   | GAS
   | JUMPDEST
   | DUP1
   | DUP2
   | DUP3
   | DUP4
   | DUP5
   | DUP6
   | DUP7
   | DUP8
   | DUP9
   | DUP10
   | DUP11
   | DUP12
   | DUP13
   | DUP14
   | DUP15
   | DUP16
   | SWAP1
   | SWAP2
   | SWAP3
   | SWAP4
   | SWAP5
   | SWAP6
   | SWAP7
   | SWAP8
   | SWAP9
   | SWAP10
   | SWAP11
   | SWAP12
   | SWAP13
   | SWAP14
   | SWAP15
   | SWAP16
   | LOG0
   | LOG1
   | LOG2
   | LOG3
   | LOG4
   | CREATE
   | CALL
   | CALLCODE
   | RETURN
   | DELEGATECALL
   | STATICCALL
   | CREATE2
   | REVERT
   | INVALID
   | SELFDESTRUCT as op ->
       let s = string_hex (get_info op).code in
       Buffer.add_string buf s
   | PUSH1 i
   | PUSH2 i
   | PUSH3 i
   | PUSH4 i
   | PUSH5 i
   | PUSH6 i
   | PUSH7 i
   | PUSH8 i
   | PUSH9 i
   | PUSH10 i
   | PUSH11 i
   | PUSH12 i
   | PUSH13 i
   | PUSH14 i
   | PUSH15 i
   | PUSH16 i
   | PUSH17 i
   | PUSH18 i
   | PUSH19 i
   | PUSH20 i
   | PUSH21 i
   | PUSH22 i
   | PUSH23 i
   | PUSH24 i
   | PUSH25 i
   | PUSH26 i
   | PUSH27 i
   | PUSH28 i
   | PUSH29 i
   | PUSH30 i
   | PUSH31 i
   | PUSH32 i as op ->
       let info = get_info op in
       let size = info.pushed in
       assert ( BigInt.sign i >= 0  || size = 32 );
       Buffer.add_string buf (string_hex info.code);
       Buffer.add_string buf (print_int_hex size i)

let print_human fmt = function
  | STOP
  | ADD
  | SUB
  | MUL
  | DIV
  | SDIV
  | MOD
  | SMOD
  | EXP
  | NOT
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | BYTE
  | SHL
  | SHR
  | SAR
  | ADDMOD
  | MULMOD
  | SIGNEXTEND
  | KECCAK256
  | ADDRESS
  | BALANCE
  | ORIGIN
  | CALLER
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | CODESIZE
  | CODECOPY
  | GASPRICE
  | EXTCODESIZE
  | EXTCODECOPY
  | RETURNDATASIZE
  | RETURNDATACOPY
  | EXTCODEHASH
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | DIFFICULTY
  | GASLIMIT
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | PC
  | MSIZE
  | GAS
  | JUMPDEST
  | DUP1
  | DUP2
  | DUP3
  | DUP4
  | DUP5
  | DUP6
  | DUP7
  | DUP8
  | DUP9
  | DUP10
  | DUP11
  | DUP12
  | DUP13
  | DUP14
  | DUP15
  | DUP16
  | SWAP1
  | SWAP2
  | SWAP3
  | SWAP4
  | SWAP5
  | SWAP6
  | SWAP7
  | SWAP8
  | SWAP9
  | SWAP10
  | SWAP11
  | SWAP12
  | SWAP13
  | SWAP14
  | SWAP15
  | SWAP16
  | LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
  | DELEGATECALL
  | STATICCALL
  | CREATE2
  | REVERT
  | INVALID
  | SELFDESTRUCT as op ->
      Format.pp_print_string fmt (get_info op).name
  | PUSH1 i
  | PUSH2 i
  | PUSH3 i
  | PUSH4 i
  | PUSH5 i
  | PUSH6 i
  | PUSH7 i
  | PUSH8 i
  | PUSH9 i
  | PUSH10 i
  | PUSH11 i
  | PUSH12 i
  | PUSH13 i
  | PUSH14 i
  | PUSH15 i
  | PUSH16 i
  | PUSH17 i
  | PUSH18 i
  | PUSH19 i
  | PUSH20 i
  | PUSH21 i
  | PUSH22 i
  | PUSH23 i
  | PUSH24 i
  | PUSH25 i
  | PUSH26 i
  | PUSH27 i
  | PUSH28 i
  | PUSH29 i
  | PUSH30 i
  | PUSH31 i
  | PUSH32 i as op ->
      let info = get_info op in
      let size = info.pushed in
      Format.fprintf fmt "%s(%s)"
        (get_info op).name
        (print_int_hex size i)

  let print_humanl fmt l =
    Format.fprintf fmt "%a@." (Pp.print_list Pp.comma print_human) l

  let print_code fmt l =
    let buf = Buffer.create 100 in
    List.iter (pp_ascii buf) l;
    Format.pp_print_string fmt (Buffer.contents buf);
    Format.pp_print_flush fmt ()


end

module EVMSimple = struct

  type label = {
    id: int;
    label_name: string;
    mutable label_addr: BigInt.t;
    (** set once all the code is known *)
    label_follow_addgas: bool; (** indicate if we follow it through addgas *)
    mutable label_index: int;
  }

  type addgas =
    | Addgas of BigInt.t * BigInt.t
    | Startgas of int
    | Stopgas of int

  type instruction =
   | STOP
   | ADD
   | SUB
   | MUL
   | DIV
   | SDIV
   | MOD
   | SMOD
   | EXP
   | NOT
   | LT
   | GT
   | SLT
   | SGT
   | EQ
   | ISZERO
   | AND
   | OR
   | XOR
   | BYTE
   | SHL
   | SHR
   | SAR
   | ADDMOD
   | MULMOD
   | SIGNEXTEND
   | KECCAK256
   | ADDRESS
   | BALANCE
   | ORIGIN
   | CALLER
   | CALLVALUE
   | CALLDATALOAD
   | CALLDATASIZE
   | CALLDATACOPY
   | CODESIZE
   | CODECOPY
   | GASPRICE
   | EXTCODESIZE
   | EXTCODECOPY
   | RETURNDATASIZE
   | RETURNDATACOPY
   | EXTCODEHASH
   | BLOCKHASH
   | COINBASE
   | TIMESTAMP
   | NUMBER
   | DIFFICULTY
   | GASLIMIT
   | POP
   | MLOAD
   | MSTORE
   | MSTORE8
   | SLOAD
   | SSTORE
   | JUMPDEST of label
   | JUMP of label
   | JUMPDYN
   | JUMPI of label
   | PUSHLABEL of label
   | PC
   | MSIZE
   | GAS
   | ADDGAS of addgas
   | PUSH1 of BigInt.t
   | PUSH2 of BigInt.t
   | PUSH3 of BigInt.t
   | PUSH4 of BigInt.t
   | PUSH5 of BigInt.t
   | PUSH6 of BigInt.t
   | PUSH7 of BigInt.t
   | PUSH8 of BigInt.t
   | PUSH9 of BigInt.t
   | PUSH10 of BigInt.t
   | PUSH11 of BigInt.t
   | PUSH12 of BigInt.t
   | PUSH13 of BigInt.t
   | PUSH14 of BigInt.t
   | PUSH15 of BigInt.t
   | PUSH16 of BigInt.t
   | PUSH17 of BigInt.t
   | PUSH18 of BigInt.t
   | PUSH19 of BigInt.t
   | PUSH20 of BigInt.t
   | PUSH21 of BigInt.t
   | PUSH22 of BigInt.t
   | PUSH23 of BigInt.t
   | PUSH24 of BigInt.t
   | PUSH25 of BigInt.t
   | PUSH26 of BigInt.t
   | PUSH27 of BigInt.t
   | PUSH28 of BigInt.t
   | PUSH29 of BigInt.t
   | PUSH30 of BigInt.t
   | PUSH31 of BigInt.t
   | PUSH32 of BigInt.t
   | DUP1
   | DUP2
   | DUP3
   | DUP4
   | DUP5
   | DUP6
   | DUP7
   | DUP8
   | DUP9
   | DUP10
   | DUP11
   | DUP12
   | DUP13
   | DUP14
   | DUP15
   | DUP16
   | SWAP1
   | SWAP2
   | SWAP3
   | SWAP4
   | SWAP5
   | SWAP6
   | SWAP7
   | SWAP8
   | SWAP9
   | SWAP10
   | SWAP11
   | SWAP12
   | SWAP13
   | SWAP14
   | SWAP15
   | SWAP16
   | LOG0
   | LOG1
   | LOG2
   | LOG3
   | LOG4
   | CREATE
   | CALL
   | CALLCODE
   | RETURN
   | DELEGATECALL
   | STATICCALL
   | CREATE2
   | REVERT
   | INVALID
   | SELFDESTRUCT
   | ALLOCATE of label * label * BigInt.t option (** None dynamic size *)

  let get_args_ret instr =
    let get_args_ret asm =
      let info = EVM.get_info asm in
      info.EVM.args, info.EVM.ret
    in
    match instr with
    | STOP -> get_args_ret EVM.STOP
    | ADD -> get_args_ret EVM.ADD
    | SUB -> get_args_ret EVM.SUB
    | MUL -> get_args_ret EVM.MUL
    | DIV -> get_args_ret EVM.DIV
    | SDIV -> get_args_ret EVM.SDIV
    | MOD -> get_args_ret EVM.MOD
    | SMOD -> get_args_ret EVM.SMOD
    | EXP -> get_args_ret EVM.EXP
    | NOT -> get_args_ret EVM.NOT
    | LT -> get_args_ret EVM.LT
    | GT -> get_args_ret EVM.GT
    | SLT -> get_args_ret EVM.SLT
    | SGT -> get_args_ret EVM.SGT
    | EQ -> get_args_ret EVM.EQ
    | ISZERO -> get_args_ret EVM.ISZERO
    | AND -> get_args_ret EVM.AND
    | OR -> get_args_ret EVM.OR
    | XOR -> get_args_ret EVM.XOR
    | BYTE -> get_args_ret EVM.BYTE
    | SHL -> get_args_ret EVM.SHL
    | SHR -> get_args_ret EVM.SHR
    | SAR -> get_args_ret EVM.SAR
    | ADDMOD -> get_args_ret EVM.ADDMOD
    | MULMOD -> get_args_ret EVM.MULMOD
    | SIGNEXTEND -> get_args_ret EVM.SIGNEXTEND
    | KECCAK256 -> get_args_ret EVM.KECCAK256
    | ADDRESS -> get_args_ret EVM.ADDRESS
    | BALANCE -> get_args_ret EVM.BALANCE
    | ORIGIN -> get_args_ret EVM.ORIGIN
    | CALLER -> get_args_ret EVM.CALLER
    | CALLVALUE -> get_args_ret EVM.CALLVALUE
    | CALLDATALOAD -> get_args_ret EVM.CALLDATALOAD
    | CALLDATASIZE -> get_args_ret EVM.CALLDATASIZE
    | CALLDATACOPY -> get_args_ret EVM.CALLDATACOPY
    | CODESIZE -> get_args_ret EVM.CODESIZE
    | CODECOPY -> get_args_ret EVM.CODECOPY
    | GASPRICE -> get_args_ret EVM.GASPRICE
    | EXTCODESIZE -> get_args_ret EVM.EXTCODESIZE
    | EXTCODECOPY -> get_args_ret EVM.EXTCODECOPY
    | RETURNDATASIZE -> get_args_ret EVM.RETURNDATASIZE
    | RETURNDATACOPY -> get_args_ret EVM.RETURNDATACOPY
    | EXTCODEHASH -> get_args_ret EVM.EXTCODEHASH
    | BLOCKHASH -> get_args_ret EVM.BLOCKHASH
    | COINBASE -> get_args_ret EVM.COINBASE
    | TIMESTAMP -> get_args_ret EVM.TIMESTAMP
    | NUMBER -> get_args_ret EVM.NUMBER
    | DIFFICULTY -> get_args_ret EVM.DIFFICULTY
    | GASLIMIT -> get_args_ret EVM.GASLIMIT
    | POP -> get_args_ret EVM.POP
    | MLOAD -> get_args_ret EVM.MLOAD
    | MSTORE -> get_args_ret EVM.MSTORE
    | MSTORE8 -> get_args_ret EVM.MSTORE8
    | SLOAD -> get_args_ret EVM.SLOAD
    | SSTORE -> get_args_ret EVM.SSTORE
    | JUMP _ -> get_args_ret EVM.JUMP
    | JUMPDYN -> get_args_ret EVM.JUMP
    | JUMPI _ -> get_args_ret EVM.JUMPI
    | PUSHLABEL lab -> get_args_ret (EVM.PUSH32 lab.label_addr)
    | PC -> get_args_ret EVM.PC
    | MSIZE -> get_args_ret EVM.MSIZE
    | GAS -> get_args_ret EVM.GAS
    | JUMPDEST _ -> get_args_ret EVM.JUMPDEST
    | PUSH1 x -> get_args_ret (EVM.PUSH1 x)
    | PUSH2 x -> get_args_ret (EVM.PUSH2 x)
    | PUSH3 x -> get_args_ret (EVM.PUSH3 x)
    | PUSH4 x -> get_args_ret (EVM.PUSH4 x)
    | PUSH5 x -> get_args_ret (EVM.PUSH5 x)
    | PUSH6 x -> get_args_ret (EVM.PUSH6 x)
    | PUSH7 x -> get_args_ret (EVM.PUSH7 x)
    | PUSH8 x -> get_args_ret (EVM.PUSH8 x)
    | PUSH9 x -> get_args_ret (EVM.PUSH9 x)
    | PUSH10 x -> get_args_ret (EVM.PUSH10 x)
    | PUSH11 x -> get_args_ret (EVM.PUSH11 x)
    | PUSH12 x -> get_args_ret (EVM.PUSH12 x)
    | PUSH13 x -> get_args_ret (EVM.PUSH13 x)
    | PUSH14 x -> get_args_ret (EVM.PUSH14 x)
    | PUSH15 x -> get_args_ret (EVM.PUSH15 x)
    | PUSH16 x -> get_args_ret (EVM.PUSH16 x)
    | PUSH17 x -> get_args_ret (EVM.PUSH17 x)
    | PUSH18 x -> get_args_ret (EVM.PUSH18 x)
    | PUSH19 x -> get_args_ret (EVM.PUSH19 x)
    | PUSH20 x -> get_args_ret (EVM.PUSH20 x)
    | PUSH21 x -> get_args_ret (EVM.PUSH21 x)
    | PUSH22 x -> get_args_ret (EVM.PUSH22 x)
    | PUSH23 x -> get_args_ret (EVM.PUSH23 x)
    | PUSH24 x -> get_args_ret (EVM.PUSH24 x)
    | PUSH25 x -> get_args_ret (EVM.PUSH25 x)
    | PUSH26 x -> get_args_ret (EVM.PUSH26 x)
    | PUSH27 x -> get_args_ret (EVM.PUSH27 x)
    | PUSH28 x -> get_args_ret (EVM.PUSH28 x)
    | PUSH29 x -> get_args_ret (EVM.PUSH29 x)
    | PUSH30 x -> get_args_ret (EVM.PUSH30 x)
    | PUSH31 x -> get_args_ret (EVM.PUSH31 x)
    | PUSH32 x -> get_args_ret (EVM.PUSH32 x)
    | DUP1 -> get_args_ret EVM.DUP1
    | DUP2 -> get_args_ret EVM.DUP2
    | DUP3 -> get_args_ret EVM.DUP3
    | DUP4 -> get_args_ret EVM.DUP4
    | DUP5 -> get_args_ret EVM.DUP5
    | DUP6 -> get_args_ret EVM.DUP6
    | DUP7 -> get_args_ret EVM.DUP7
    | DUP8 -> get_args_ret EVM.DUP8
    | DUP9 -> get_args_ret EVM.DUP9
    | DUP10 -> get_args_ret EVM.DUP10
    | DUP11 -> get_args_ret EVM.DUP11
    | DUP12 -> get_args_ret EVM.DUP12
    | DUP13 -> get_args_ret EVM.DUP13
    | DUP14 -> get_args_ret EVM.DUP14
    | DUP15 -> get_args_ret EVM.DUP15
    | DUP16 -> get_args_ret EVM.DUP16
    | SWAP1 -> get_args_ret EVM.SWAP1
    | SWAP2 -> get_args_ret EVM.SWAP2
    | SWAP3 -> get_args_ret EVM.SWAP3
    | SWAP4 -> get_args_ret EVM.SWAP4
    | SWAP5 -> get_args_ret EVM.SWAP5
    | SWAP6 -> get_args_ret EVM.SWAP6
    | SWAP7 -> get_args_ret EVM.SWAP7
    | SWAP8 -> get_args_ret EVM.SWAP8
    | SWAP9 -> get_args_ret EVM.SWAP9
    | SWAP10 -> get_args_ret EVM.SWAP10
    | SWAP11 -> get_args_ret EVM.SWAP11
    | SWAP12 -> get_args_ret EVM.SWAP12
    | SWAP13 -> get_args_ret EVM.SWAP13
    | SWAP14 -> get_args_ret EVM.SWAP14
    | SWAP15 -> get_args_ret EVM.SWAP15
    | SWAP16 -> get_args_ret EVM.SWAP16
    | LOG0 -> get_args_ret EVM.LOG0
    | LOG1 -> get_args_ret EVM.LOG1
    | LOG2 -> get_args_ret EVM.LOG2
    | LOG3 -> get_args_ret EVM.LOG3
    | LOG4 -> get_args_ret EVM.LOG4
    | CREATE -> get_args_ret EVM.CREATE
    | CALL -> get_args_ret EVM.CALL
    | CALLCODE -> get_args_ret EVM.CALLCODE
    | RETURN -> get_args_ret EVM.RETURN
    | DELEGATECALL -> get_args_ret EVM.DELEGATECALL
    | STATICCALL -> get_args_ret EVM.STATICCALL
    | CREATE2 -> get_args_ret EVM.CREATE2
    | REVERT -> get_args_ret EVM.REVERT
    | INVALID -> get_args_ret EVM.INVALID
    | SELFDESTRUCT -> get_args_ret EVM.SELFDESTRUCT
    | ADDGAS _ -> 0,0
    | ALLOCATE (_,_,Some _) -> 0,1
    | ALLOCATE (_,_,None) -> 1,1

  let get_name instr =
    let aux asm =
      let info = EVM.get_info asm in
      info.EVM.name
    in
    match instr with
    | STOP -> aux EVM.STOP
    | ADD -> aux EVM.ADD
    | SUB -> aux EVM.SUB
    | MUL -> aux EVM.MUL
    | DIV -> aux EVM.DIV
    | SDIV -> aux EVM.SDIV
    | MOD -> aux EVM.MOD
    | SMOD -> aux EVM.SMOD
    | EXP -> aux EVM.EXP
    | NOT -> aux EVM.NOT
    | LT -> aux EVM.LT
    | GT -> aux EVM.GT
    | SLT -> aux EVM.SLT
    | SGT -> aux EVM.SGT
    | EQ -> aux EVM.EQ
    | ISZERO -> aux EVM.ISZERO
    | AND -> aux EVM.AND
    | OR -> aux EVM.OR
    | XOR -> aux EVM.XOR
    | BYTE -> aux EVM.BYTE
    | SHL -> aux EVM.SHL
    | SHR -> aux EVM.SHR
    | SAR -> aux EVM.SAR
    | ADDMOD -> aux EVM.ADDMOD
    | MULMOD -> aux EVM.MULMOD
    | SIGNEXTEND -> aux EVM.SIGNEXTEND
    | KECCAK256 -> aux EVM.KECCAK256
    | ADDRESS -> aux EVM.ADDRESS
    | BALANCE -> aux EVM.BALANCE
    | ORIGIN -> aux EVM.ORIGIN
    | CALLER -> aux EVM.CALLER
    | CALLVALUE -> aux EVM.CALLVALUE
    | CALLDATALOAD -> aux EVM.CALLDATALOAD
    | CALLDATASIZE -> aux EVM.CALLDATASIZE
    | CALLDATACOPY -> aux EVM.CALLDATACOPY
    | CODESIZE -> aux EVM.CODESIZE
    | CODECOPY -> aux EVM.CODECOPY
    | GASPRICE -> aux EVM.GASPRICE
    | EXTCODESIZE -> aux EVM.EXTCODESIZE
    | EXTCODECOPY -> aux EVM.EXTCODECOPY
    | RETURNDATASIZE -> aux EVM.RETURNDATASIZE
    | RETURNDATACOPY -> aux EVM.RETURNDATACOPY
    | EXTCODEHASH -> aux EVM.EXTCODEHASH
    | BLOCKHASH -> aux EVM.BLOCKHASH
    | COINBASE -> aux EVM.COINBASE
    | TIMESTAMP -> aux EVM.TIMESTAMP
    | NUMBER -> aux EVM.NUMBER
    | DIFFICULTY -> aux EVM.DIFFICULTY
    | GASLIMIT -> aux EVM.GASLIMIT
    | POP -> aux EVM.POP
    | MLOAD -> aux EVM.MLOAD
    | MSTORE -> aux EVM.MSTORE
    | MSTORE8 -> aux EVM.MSTORE8
    | SLOAD -> aux EVM.SLOAD
    | SSTORE -> aux EVM.SSTORE
    | JUMP _ -> aux EVM.JUMP
    | JUMPDYN -> aux EVM.JUMP
    | JUMPI _ -> aux EVM.JUMPI
    | PUSHLABEL lab -> aux (EVM.PUSH32 lab.label_addr)
    | PC -> aux EVM.PC
    | MSIZE -> aux EVM.MSIZE
    | GAS -> aux EVM.GAS
    | JUMPDEST _ -> aux EVM.JUMPDEST
    | PUSH1 x -> aux (EVM.PUSH1 x)
    | PUSH2 x -> aux (EVM.PUSH2 x)
    | PUSH3 x -> aux (EVM.PUSH3 x)
    | PUSH4 x -> aux (EVM.PUSH4 x)
    | PUSH5 x -> aux (EVM.PUSH5 x)
    | PUSH6 x -> aux (EVM.PUSH6 x)
    | PUSH7 x -> aux (EVM.PUSH7 x)
    | PUSH8 x -> aux (EVM.PUSH8 x)
    | PUSH9 x -> aux (EVM.PUSH9 x)
    | PUSH10 x -> aux (EVM.PUSH10 x)
    | PUSH11 x -> aux (EVM.PUSH11 x)
    | PUSH12 x -> aux (EVM.PUSH12 x)
    | PUSH13 x -> aux (EVM.PUSH13 x)
    | PUSH14 x -> aux (EVM.PUSH14 x)
    | PUSH15 x -> aux (EVM.PUSH15 x)
    | PUSH16 x -> aux (EVM.PUSH16 x)
    | PUSH17 x -> aux (EVM.PUSH17 x)
    | PUSH18 x -> aux (EVM.PUSH18 x)
    | PUSH19 x -> aux (EVM.PUSH19 x)
    | PUSH20 x -> aux (EVM.PUSH20 x)
    | PUSH21 x -> aux (EVM.PUSH21 x)
    | PUSH22 x -> aux (EVM.PUSH22 x)
    | PUSH23 x -> aux (EVM.PUSH23 x)
    | PUSH24 x -> aux (EVM.PUSH24 x)
    | PUSH25 x -> aux (EVM.PUSH25 x)
    | PUSH26 x -> aux (EVM.PUSH26 x)
    | PUSH27 x -> aux (EVM.PUSH27 x)
    | PUSH28 x -> aux (EVM.PUSH28 x)
    | PUSH29 x -> aux (EVM.PUSH29 x)
    | PUSH30 x -> aux (EVM.PUSH30 x)
    | PUSH31 x -> aux (EVM.PUSH31 x)
    | PUSH32 x -> aux (EVM.PUSH32 x)
    | DUP1 -> aux EVM.DUP1
    | DUP2 -> aux EVM.DUP2
    | DUP3 -> aux EVM.DUP3
    | DUP4 -> aux EVM.DUP4
    | DUP5 -> aux EVM.DUP5
    | DUP6 -> aux EVM.DUP6
    | DUP7 -> aux EVM.DUP7
    | DUP8 -> aux EVM.DUP8
    | DUP9 -> aux EVM.DUP9
    | DUP10 -> aux EVM.DUP10
    | DUP11 -> aux EVM.DUP11
    | DUP12 -> aux EVM.DUP12
    | DUP13 -> aux EVM.DUP13
    | DUP14 -> aux EVM.DUP14
    | DUP15 -> aux EVM.DUP15
    | DUP16 -> aux EVM.DUP16
    | SWAP1 -> aux EVM.SWAP1
    | SWAP2 -> aux EVM.SWAP2
    | SWAP3 -> aux EVM.SWAP3
    | SWAP4 -> aux EVM.SWAP4
    | SWAP5 -> aux EVM.SWAP5
    | SWAP6 -> aux EVM.SWAP6
    | SWAP7 -> aux EVM.SWAP7
    | SWAP8 -> aux EVM.SWAP8
    | SWAP9 -> aux EVM.SWAP9
    | SWAP10 -> aux EVM.SWAP10
    | SWAP11 -> aux EVM.SWAP11
    | SWAP12 -> aux EVM.SWAP12
    | SWAP13 -> aux EVM.SWAP13
    | SWAP14 -> aux EVM.SWAP14
    | SWAP15 -> aux EVM.SWAP15
    | SWAP16 -> aux EVM.SWAP16
    | LOG0 -> aux EVM.LOG0
    | LOG1 -> aux EVM.LOG1
    | LOG2 -> aux EVM.LOG2
    | LOG3 -> aux EVM.LOG3
    | LOG4 -> aux EVM.LOG4
    | CREATE -> aux EVM.CREATE
    | CALL -> aux EVM.CALL
    | CALLCODE -> aux EVM.CALLCODE
    | RETURN -> aux EVM.RETURN
    | DELEGATECALL -> aux EVM.DELEGATECALL
    | STATICCALL -> aux EVM.STATICCALL
    | CREATE2 -> aux EVM.CREATE2
    | REVERT -> aux EVM.REVERT
    | INVALID -> aux EVM.INVALID
    | SELFDESTRUCT -> aux EVM.SELFDESTRUCT
    | ADDGAS (Addgas _) -> "ADDGAS"
    | ADDGAS (Startgas _) -> "STARTGAS"
    | ADDGAS (Stopgas _) -> "STOPGAS"
    | ALLOCATE (_,_,_) -> "ALLOCATE"

  let pc_to_num pc =
    let n = BigInt.num_bits pc in
    (n-1) / 8

  let pc_to_push pc =
    let n = pc_to_num pc in
    match n with
    | 0 -> EVM.PUSH1 pc
    | 1 -> EVM.PUSH2 pc
    | 2 -> EVM.PUSH3 pc
    | 3 -> EVM.PUSH4 pc
    | 4 -> EVM.PUSH5 pc
    | 5 -> EVM.PUSH6 pc
    | 6 -> EVM.PUSH7 pc
    | 7 -> EVM.PUSH8 pc
    | 8 -> EVM.PUSH9 pc
    | 9 -> EVM.PUSH10 pc
    | 10 -> EVM.PUSH11 pc
    | 11 -> EVM.PUSH12 pc
    | 12 -> EVM.PUSH13 pc
    | 13 -> EVM.PUSH14 pc
    | 14 -> EVM.PUSH15 pc
    | 15 -> EVM.PUSH16 pc
    | 16 -> EVM.PUSH17 pc
    | 17 -> EVM.PUSH18 pc
    | 18 -> EVM.PUSH19 pc
    | 19 -> EVM.PUSH20 pc
    | 20 -> EVM.PUSH21 pc
    | 21 -> EVM.PUSH22 pc
    | 22 -> EVM.PUSH23 pc
    | 23 -> EVM.PUSH24 pc
    | 24 -> EVM.PUSH25 pc
    | 25 -> EVM.PUSH26 pc
    | 26 -> EVM.PUSH27 pc
    | 27 -> EVM.PUSH28 pc
    | 28 -> EVM.PUSH29 pc
    | 29 -> EVM.PUSH30 pc
    | 30 -> EVM.PUSH31 pc
    | 31 -> EVM.PUSH32 pc
    | _ -> assert false

  let num_to_push i =
    if BigInt.sign i < 0 then
      PUSH32 i
    else
      let n = pc_to_num i in
      match n with
      | 0 -> PUSH1 i
      | 1 -> PUSH2 i
      | 2 -> PUSH3 i
      | 3 -> PUSH4 i
      | 4 -> PUSH5 i
      | 5 -> PUSH6 i
      | 6 -> PUSH7 i
      | 7 -> PUSH8 i
      | 8 -> PUSH9 i
      | 9 -> PUSH10 i
      | 10 -> PUSH11 i
      | 11 -> PUSH12 i
      | 12 -> PUSH13 i
      | 13 -> PUSH14 i
      | 14 -> PUSH15 i
      | 15 -> PUSH16 i
      | 16 -> PUSH17 i
      | 17 -> PUSH18 i
      | 18 -> PUSH19 i
      | 19 -> PUSH20 i
      | 20 -> PUSH21 i
      | 21 -> PUSH22 i
      | 22 -> PUSH23 i
      | 23 -> PUSH24 i
      | 24 -> PUSH25 i
      | 25 -> PUSH26 i
      | 26 -> PUSH27 i
      | 27 -> PUSH28 i
      | 28 -> PUSH29 i
      | 29 -> PUSH30 i
      | 30 -> PUSH31 i
      | 31 -> PUSH32 i
      | _ -> assert false

  let int_to_push i = num_to_push (BigInt.of_int i)

  let swap i =
    match i - 2 with
    | x when x < 0 -> invalid_arg "nothing to swap: swap smaller than 2"
    | 0 -> SWAP1
    | 1 -> SWAP2
    | 2 -> SWAP3
    | 3 -> SWAP4
    | 4 -> SWAP5
    | 5 -> SWAP6
    | 6 -> SWAP7
    | 7 -> SWAP8
    | 8 -> SWAP9
    | 9 -> SWAP10
    | 10 -> SWAP11
    | 11 -> SWAP12
    | 12 -> SWAP13
    | 13 -> SWAP14
    | 14 -> SWAP15
    | 15 -> SWAP16
    | _ -> invalid_arg "Can't swap that much"

    let dup = function
    | x when x <= 0 -> invalid_arg "dup <= 0"
    | 1 -> DUP1
    | 2 -> DUP2
    | 3 -> DUP3
    | 4 -> DUP4
    | 5 -> DUP5
    | 6 -> DUP6
    | 7 -> DUP7
    | 8 -> DUP8
    | 9 -> DUP9
    | 10 -> DUP10
    | 11 -> DUP11
    | 12 -> DUP12
    | 13 -> DUP13
    | 14 -> DUP14
    | 15 -> DUP15
    | 16 -> DUP16
    | _ -> invalid_arg "get_var too far"

    let allocate_code label_ret label_call size  =
      [
        PUSHLABEL label_ret;
        (match size with | Some size -> num_to_push size | None -> SWAP1);
        JUMP label_call;
        JUMPDEST label_ret]

  let rec to_evm = function
   | STOP -> [EVM.STOP]
   | ADD -> [EVM.ADD]
   | SUB -> [EVM.SUB]
   | MUL -> [EVM.MUL]
   | DIV -> [EVM.DIV]
   | SDIV -> [EVM.SDIV]
   | MOD -> [EVM.MOD]
   | SMOD -> [EVM.SMOD]
   | EXP -> [EVM.EXP]
   | NOT -> [EVM.NOT]
   | LT -> [EVM.LT]
   | GT -> [EVM.GT]
   | SLT -> [EVM.SLT]
   | SGT -> [EVM.SGT]
   | EQ -> [EVM.EQ]
   | ISZERO -> [EVM.ISZERO]
   | AND -> [EVM.AND]
   | OR -> [EVM.OR]
   | XOR -> [EVM.XOR]
   | BYTE -> [EVM.BYTE]
   | SHL -> [EVM.SHL]
   | SHR -> [EVM.SHR]
   | SAR -> [EVM.SAR]
   | ADDMOD -> [EVM.ADDMOD]
   | MULMOD -> [EVM.MULMOD]
   | SIGNEXTEND -> [EVM.SIGNEXTEND]
   | KECCAK256 -> [EVM.KECCAK256]
   | ADDRESS -> [EVM.ADDRESS]
   | BALANCE -> [EVM.BALANCE]
   | ORIGIN -> [EVM.ORIGIN]
   | CALLER -> [EVM.CALLER]
   | CALLVALUE -> [EVM.CALLVALUE]
   | CALLDATALOAD -> [EVM.CALLDATALOAD]
   | CALLDATASIZE -> [EVM.CALLDATASIZE]
   | CALLDATACOPY -> [EVM.CALLDATACOPY]
   | CODESIZE -> [EVM.CODESIZE]
   | CODECOPY -> [EVM.CODECOPY]
   | GASPRICE -> [EVM.GASPRICE]
   | EXTCODESIZE -> [EVM.EXTCODESIZE]
   | EXTCODECOPY -> [EVM.EXTCODECOPY]
   | RETURNDATASIZE -> [EVM.RETURNDATASIZE]
   | RETURNDATACOPY -> [EVM.RETURNDATACOPY]
   | EXTCODEHASH -> [EVM.EXTCODEHASH]
   | BLOCKHASH -> [EVM.BLOCKHASH]
   | COINBASE -> [EVM.COINBASE]
   | TIMESTAMP -> [EVM.TIMESTAMP]
   | NUMBER -> [EVM.NUMBER]
   | DIFFICULTY -> [EVM.DIFFICULTY]
   | GASLIMIT -> [EVM.GASLIMIT]
   | POP -> [EVM.POP]
   | MLOAD -> [EVM.MLOAD]
   | MSTORE -> [EVM.MSTORE]
   | MSTORE8 -> [EVM.MSTORE8]
   | SLOAD -> [EVM.SLOAD]
   | SSTORE -> [EVM.SSTORE]
   | JUMP label -> [pc_to_push label.label_addr;EVM.JUMP]
   | JUMPDYN -> [EVM.JUMP]
   | JUMPI label -> [pc_to_push label.label_addr;EVM.JUMPI]
   | PUSHLABEL label -> [pc_to_push label.label_addr]
   | PC -> [EVM.PC]
   | MSIZE -> [EVM.MSIZE]
   | GAS -> [EVM.GAS]
   | ADDGAS _ -> []
   | JUMPDEST label ->
       Debug.dprintf debug "JUMPDEST: %s %s %s@." (EVM.print_int_hex 4 label.label_addr) (BigInt.to_string label.label_addr) label.label_name;
       [EVM.JUMPDEST]
   | PUSH1 x -> [(EVM.PUSH1 x)]
   | PUSH2 x -> [(EVM.PUSH2 x)]
   | PUSH3 x -> [(EVM.PUSH3 x)]
   | PUSH4 x -> [(EVM.PUSH4 x)]
   | PUSH5 x -> [(EVM.PUSH5 x)]
   | PUSH6 x -> [(EVM.PUSH6 x)]
   | PUSH7 x -> [(EVM.PUSH7 x)]
   | PUSH8 x -> [(EVM.PUSH8 x)]
   | PUSH9 x -> [(EVM.PUSH9 x)]
   | PUSH10 x -> [(EVM.PUSH10 x)]
   | PUSH11 x -> [(EVM.PUSH11 x)]
   | PUSH12 x -> [(EVM.PUSH12 x)]
   | PUSH13 x -> [(EVM.PUSH13 x)]
   | PUSH14 x -> [(EVM.PUSH14 x)]
   | PUSH15 x -> [(EVM.PUSH15 x)]
   | PUSH16 x -> [(EVM.PUSH16 x)]
   | PUSH17 x -> [(EVM.PUSH17 x)]
   | PUSH18 x -> [(EVM.PUSH18 x)]
   | PUSH19 x -> [(EVM.PUSH19 x)]
   | PUSH20 x -> [(EVM.PUSH20 x)]
   | PUSH21 x -> [(EVM.PUSH21 x)]
   | PUSH22 x -> [(EVM.PUSH22 x)]
   | PUSH23 x -> [(EVM.PUSH23 x)]
   | PUSH24 x -> [(EVM.PUSH24 x)]
   | PUSH25 x -> [(EVM.PUSH25 x)]
   | PUSH26 x -> [(EVM.PUSH26 x)]
   | PUSH27 x -> [(EVM.PUSH27 x)]
   | PUSH28 x -> [(EVM.PUSH28 x)]
   | PUSH29 x -> [(EVM.PUSH29 x)]
   | PUSH30 x -> [(EVM.PUSH30 x)]
   | PUSH31 x -> [(EVM.PUSH31 x)]
   | PUSH32 x -> [(EVM.PUSH32 x)]
   | DUP1 -> [EVM.DUP1]
   | DUP2 -> [EVM.DUP2]
   | DUP3 -> [EVM.DUP3]
   | DUP4 -> [EVM.DUP4]
   | DUP5 -> [EVM.DUP5]
   | DUP6 -> [EVM.DUP6]
   | DUP7 -> [EVM.DUP7]
   | DUP8 -> [EVM.DUP8]
   | DUP9 -> [EVM.DUP9]
   | DUP10 -> [EVM.DUP10]
   | DUP11 -> [EVM.DUP11]
   | DUP12 -> [EVM.DUP12]
   | DUP13 -> [EVM.DUP13]
   | DUP14 -> [EVM.DUP14]
   | DUP15 -> [EVM.DUP15]
   | DUP16 -> [EVM.DUP16]
   | SWAP1 -> [EVM.SWAP1]
   | SWAP2 -> [EVM.SWAP2]
   | SWAP3 -> [EVM.SWAP3]
   | SWAP4 -> [EVM.SWAP4]
   | SWAP5 -> [EVM.SWAP5]
   | SWAP6 -> [EVM.SWAP6]
   | SWAP7 -> [EVM.SWAP7]
   | SWAP8 -> [EVM.SWAP8]
   | SWAP9 -> [EVM.SWAP9]
   | SWAP10 -> [EVM.SWAP10]
   | SWAP11 -> [EVM.SWAP11]
   | SWAP12 -> [EVM.SWAP12]
   | SWAP13 -> [EVM.SWAP13]
   | SWAP14 -> [EVM.SWAP14]
   | SWAP15 -> [EVM.SWAP15]
   | SWAP16 -> [EVM.SWAP16]
   | LOG0 -> [EVM.LOG0]
   | LOG1 -> [EVM.LOG1]
   | LOG2 -> [EVM.LOG2]
   | LOG3 -> [EVM.LOG3]
   | LOG4 -> [EVM.LOG4]
   | CREATE -> [EVM.CREATE]
   | CALL -> [EVM.CALL]
   | CALLCODE -> [EVM.CALLCODE]
   | RETURN -> [EVM.RETURN]
   | DELEGATECALL -> [EVM.DELEGATECALL]
   | STATICCALL -> [EVM.STATICCALL]
   | CREATE2 -> [EVM.CREATE2]
   | REVERT -> [EVM.REVERT]
   | INVALID -> [EVM.INVALID]
   | SELFDESTRUCT -> [EVM.SELFDESTRUCT]
   | ALLOCATE(label_ret,label_call,size) ->
      List.concat (List.map to_evm (allocate_code label_ret label_call size))

  type asm = {
    mutable codes: instruction list;
  }

  type stack = {
    asm: asm;
    mutable local: int Ident.Mid.t;
    global: int Ident.Mid.t;
    mutable bottom: int;
    call_labels: label Expr.Mrs.t;
  }

  let new_label =
    let label_counter = ref (-1) in
    fun ~follow name ->
      incr label_counter;
      { id = !label_counter; label_name = name; label_addr = BigInt.zero;
        label_follow_addgas = follow;
        label_index = -1;
      }

  let new_startstop_addgas =
    let label_counter = ref (-1) in
    fun () ->
      incr label_counter;
      ADDGAS (Startgas (!label_counter)),ADDGAS (Stopgas (!label_counter))

  let add ?(popped=0) ?(pushed=0) stack asm =
    stack.asm.codes <- asm::stack.asm.codes;
    stack.bottom <- stack.bottom - popped + pushed

  let add_auto stack asm =
    match asm with
    | JUMPDEST _ | JUMP _ ->
        add stack asm
    | JUMPI _ | JUMPDYN ->
        add ~popped:1 stack asm
    | PUSHLABEL _ ->
        add ~pushed:1 stack asm
    | _ ->
    let popped, pushed = get_args_ret asm in
    add stack asm ~popped ~pushed

  let jumpdest stack label =
    add_auto stack (JUMPDEST label)

  let jump stack label =
    add_auto stack (JUMP label)

  let jumpi stack label =
    add_auto stack (JUMPI label)

  let auto stack l =
    List.iter (add_auto stack) l

  let call stack ~call ~return ~args ~ret =
    auto stack [JUMP call;JUMPDEST return];
    stack.bottom <- stack.bottom - 1 (** return pc *) - args +  ret

  let bind_var stack var =
    stack.local <- Ident.Mid.add var stack.bottom stack.local

  let forget_var stack var =
    stack.local <- Ident.Mid.remove var stack.local

  let pop_var stack var =
    forget_var stack var;
    add_auto stack POP

  let add_arg stack var =
    stack.bottom <- stack.bottom + 1;
    let stack = bind_var stack var in
    stack

  let get_var stack var =
    try
      `Local (stack.bottom + 1 - Ident.Mid.find var stack.local)
    with Not_found ->
      `Global (Ident.Mid.find var stack.global)

  let is_global stack var =
    Ident.Mid.mem var stack.global

  let get_global_var stack var =
    Ident.Mid.find var stack.global

  let add_gas fmt i j =
    add_auto fmt (ADDGAS (Addgas(i,j)))

  module Allocate = struct
    let init stack =
      auto stack
        [int_to_push 0x80;
         int_to_push 0x40;
         MSTORE]

    let label = new_label ~follow:false "allocate_function"


    let code =
      [
        JUMPDEST label;
        int_to_push 0x40;
        MLOAD;
        DUP1;
        SWAP2;
        ADD;
        int_to_push 0x40;
        MSTORE;
        SWAP1;
        JUMPDYN;
      ]

    let cost =
      (EVM.costl (List.concat (List.map to_evm code)))

    let define_allocate stack =
      auto stack code

    let allocate stack size =
      let return = new_label ~follow:false "allocate_call" in
      auto stack [
        ALLOCATE(return,label,Some (BigInt.of_int size))
      ]

    let allocate_dyn stack =
      let return = new_label ~follow:false "allocate_call" in
      auto stack [
        ALLOCATE(return,label,None)
      ]

  end


  let add_auto_json fmt = function
   | Json_base.String "STOP" -> add_auto fmt STOP
   | Json_base.String "ADD" -> add_auto fmt ADD
   | Json_base.String "SUB" -> add_auto fmt SUB
   | Json_base.String "MUL" -> add_auto fmt MUL
   | Json_base.String "DIV" -> add_auto fmt DIV
   | Json_base.String "SDIV" -> add_auto fmt SDIV
   | Json_base.String "MOD" -> add_auto fmt MOD
   | Json_base.String "SMOD" -> add_auto fmt SMOD
   | Json_base.String "EXP" -> add_auto fmt EXP
   | Json_base.String "NOT" -> add_auto fmt NOT
   | Json_base.String "LT" -> add_auto fmt LT
   | Json_base.String "GT" -> add_auto fmt GT
   | Json_base.String "SLT" -> add_auto fmt SLT
   | Json_base.String "SGT" -> add_auto fmt SGT
   | Json_base.String "EQ" -> add_auto fmt EQ
   | Json_base.String "ISZERO" -> add_auto fmt ISZERO
   | Json_base.String "AND" -> add_auto fmt AND
   | Json_base.String "OR" -> add_auto fmt OR
   | Json_base.String "XOR" -> add_auto fmt XOR
   | Json_base.String "BYTE" -> add_auto fmt BYTE
   | Json_base.String "SHL" -> add_auto fmt SHL
   | Json_base.String "SHR" -> add_auto fmt SHR
   | Json_base.String "SAR" -> add_auto fmt SAR
   | Json_base.String "ADDMOD" -> add_auto fmt ADDMOD
   | Json_base.String "MULMOD" -> add_auto fmt MULMOD
   | Json_base.String "SIGNEXTEND" -> add_auto fmt SIGNEXTEND
   | Json_base.String "KECCAK256" -> add_auto fmt KECCAK256
   | Json_base.String "ADDRESS" -> add_auto fmt ADDRESS
   | Json_base.String "BALANCE" -> add_auto fmt BALANCE
   | Json_base.String "ORIGIN" -> add_auto fmt ORIGIN
   | Json_base.String "CALLER" -> add_auto fmt CALLER
   | Json_base.String "CALLVALUE" -> add_auto fmt CALLVALUE
   | Json_base.String "CALLDATALOAD" -> add_auto fmt CALLDATALOAD
   | Json_base.String "CALLDATASIZE" -> add_auto fmt CALLDATASIZE
   | Json_base.String "CALLDATACOPY" -> add_auto fmt CALLDATACOPY
   | Json_base.String "CODESIZE" -> add_auto fmt CODESIZE
   | Json_base.String "CODECOPY" -> add_auto fmt CODECOPY
   | Json_base.String "GASPRICE" -> add_auto fmt GASPRICE
   | Json_base.String "EXTCODESIZE" -> add_auto fmt EXTCODESIZE
   | Json_base.String "EXTCODECOPY" -> add_auto fmt EXTCODECOPY
   | Json_base.String "RETURNDATASIZE" -> add_auto fmt RETURNDATASIZE
   | Json_base.String "RETURNDATACOPY" -> add_auto fmt RETURNDATACOPY
   | Json_base.String "EXTCODEHASH" -> add_auto fmt EXTCODEHASH
   | Json_base.String "BLOCKHASH" -> add_auto fmt BLOCKHASH
   | Json_base.String "COINBASE" -> add_auto fmt COINBASE
   | Json_base.String "TIMESTAMP" -> add_auto fmt TIMESTAMP
   | Json_base.String "NUMBER" -> add_auto fmt NUMBER
   | Json_base.String "DIFFICULTY" -> add_auto fmt DIFFICULTY
   | Json_base.String "GASLIMIT" -> add_auto fmt GASLIMIT
   | Json_base.String "POP" -> add_auto fmt POP
   | Json_base.String "MLOAD" -> add_auto fmt MLOAD
   | Json_base.String "MSTORE" -> add_auto fmt MSTORE
   | Json_base.String "MSTORE8" -> add_auto fmt MSTORE8
   | Json_base.String "SLOAD" -> add_auto fmt SLOAD
   | Json_base.String "SSTORE" -> add_auto fmt SSTORE
   | Json_base.String "PC" -> add_auto fmt PC
   | Json_base.String "MSIZE" -> add_auto fmt MSIZE
   | Json_base.String "GAS" -> add_auto fmt GAS
   | Json_base.List [Json_base.String "PUSH1"; Json_base.Int x] -> add_auto fmt (PUSH1 (BigInt.of_int x))
   | Json_base.String "DUP1" -> add_auto fmt DUP1
   | Json_base.String "DUP2" -> add_auto fmt DUP2
   | Json_base.String "DUP3" -> add_auto fmt DUP3
   | Json_base.String "DUP4" -> add_auto fmt DUP4
   | Json_base.String "DUP5" -> add_auto fmt DUP5
   | Json_base.String "DUP6" -> add_auto fmt DUP6
   | Json_base.String "DUP7" -> add_auto fmt DUP7
   | Json_base.String "DUP8" -> add_auto fmt DUP8
   | Json_base.String "DUP9" -> add_auto fmt DUP9
   | Json_base.String "DUP10" -> add_auto fmt DUP10
   | Json_base.String "DUP11" -> add_auto fmt DUP11
   | Json_base.String "DUP12" -> add_auto fmt DUP12
   | Json_base.String "DUP13" -> add_auto fmt DUP13
   | Json_base.String "DUP14" -> add_auto fmt DUP14
   | Json_base.String "DUP15" -> add_auto fmt DUP15
   | Json_base.String "DUP16" -> add_auto fmt DUP16
   | Json_base.String "SWAP1" -> add_auto fmt SWAP1
   | Json_base.String "SWAP2" -> add_auto fmt SWAP2
   | Json_base.String "SWAP3" -> add_auto fmt SWAP3
   | Json_base.String "SWAP4" -> add_auto fmt SWAP4
   | Json_base.String "SWAP5" -> add_auto fmt SWAP5
   | Json_base.String "SWAP6" -> add_auto fmt SWAP6
   | Json_base.String "SWAP7" -> add_auto fmt SWAP7
   | Json_base.String "SWAP8" -> add_auto fmt SWAP8
   | Json_base.String "SWAP9" -> add_auto fmt SWAP9
   | Json_base.String "SWAP10" -> add_auto fmt SWAP10
   | Json_base.String "SWAP11" -> add_auto fmt SWAP11
   | Json_base.String "SWAP12" -> add_auto fmt SWAP12
   | Json_base.String "SWAP13" -> add_auto fmt SWAP13
   | Json_base.String "SWAP14" -> add_auto fmt SWAP14
   | Json_base.String "SWAP15" -> add_auto fmt SWAP15
   | Json_base.String "SWAP16" -> add_auto fmt SWAP16
   | Json_base.String "LOG0" -> add_auto fmt LOG0
   | Json_base.String "LOG1" -> add_auto fmt LOG1
   | Json_base.String "LOG2" -> add_auto fmt LOG2
   | Json_base.String "LOG3" -> add_auto fmt LOG3
   | Json_base.String "LOG4" -> add_auto fmt LOG4
   | Json_base.String "CREATE" -> add_auto fmt CREATE
   | Json_base.String "CALL" -> add_auto fmt CALL
   | Json_base.String "CALLCODE" -> add_auto fmt CALLCODE
   | Json_base.String "RETURN" -> add_auto fmt RETURN
   | Json_base.String "DELEGATECALL" -> add_auto fmt DELEGATECALL
   | Json_base.String "STATICCALL" -> add_auto fmt STATICCALL
   | Json_base.String "CREATE2" -> add_auto fmt CREATE2
   | Json_base.String "REVERT" -> add_auto fmt REVERT
   | Json_base.String "INVALID" -> add_auto fmt INVALID
   | Json_base.String "SELFDESTRUCT" -> add_auto fmt SELFDESTRUCT
   | Json_base.List [Json_base.String "ALLOCATE"; Json_base.Int x] ->
       Allocate.allocate fmt x
   | Json_base.String "ALLOCATE_DYN" ->
       Allocate.allocate_dyn fmt
   | _ -> invalid_arg "incorrect json"

  let copy_stack stack = { stack with bottom = stack.bottom }

  (** finalize *)
  let linearize l =
    let stable = ref true in
    let rec compute_label (i,pc) = function
      | JUMPDEST label ->
          let num = pc_to_num pc in
          let num' = pc_to_num label.label_addr in
          label.label_addr <- pc;
          label.label_index <- i;
          if not (num = num') then begin
            stable := false;
          end;
          i+1,BigInt.succ pc
      | ALLOCATE(label_ret,label_call,size) ->
          let l = allocate_code label_ret label_call size in
          let _,pc = List.fold_left compute_label (i,pc) l in
          i+1,pc
      | instr ->
          i+1,BigInt.add pc (BigInt.of_int (EVM.sizel (to_evm instr)))
    in
    let rec fixpoint () =
      stable := true;
      let _pc = List.fold_left compute_label (0,BigInt.zero) l in
      if not !stable then fixpoint ()
    in
    fixpoint ()

  let report name i gas =
    let c = BigInt.sign gas in
    if c > 0 then
      Format.eprintf "Not enough %s declared for %i: %s@." name i (BigInt.to_string gas)
    else if c = 0 then
      Format.eprintf "Good number of %s declared for %i@." name i
    else
      Format.eprintf "Too much %s declared for %i: %s too much@."
        name
        i (BigInt.to_string (BigInt.sub BigInt.zero gas))

  let gaz_checking l =
    (* TODO loop handling, let rec naturally handled *)
    let asmmap = Array.of_list l in
    let rec count i gas alloc pc (** in fact index *) =
      Debug.dprintf debug "%i %i: %s %s@." i pc (BigInt.to_string gas) (get_name asmmap.(pc));
      match asmmap.(pc) with
      | ADDGAS(Stopgas i') when i = i' ->
          report "gas" i gas;
          report "alloc" i alloc
      | ADDGAS(Addgas(g,a)) ->
          count i (BigInt.sub gas g) (BigInt.sub alloc a) (pc+1)
      | (ALLOCATE(_,_,Some s) as instr) ->
          let cost = (EVM.costl (to_evm instr)) in
          count i (BigInt.add (BigInt.add gas Allocate.cost) cost) (BigInt.add alloc s) (pc+1)
      | (ALLOCATE(_,_,None) as instr) ->
          let cost = (EVM.costl (to_evm instr)) in
          count i (BigInt.add (BigInt.add gas Allocate.cost) cost) alloc (pc+1)
      | (REVERT | STOP as instr) ->
          let cost = (EVM.costl (to_evm instr)) in
          let gas = (BigInt.add gas cost) in
          report "gas" i gas;
          report "alloc" i alloc
      | ((JUMP label) as instr) when label.label_follow_addgas ->
          let cost = (EVM.costl (to_evm instr)) in
          count i (BigInt.add gas cost) alloc label.label_index
      | ((JUMPI label) as instr) when label.label_follow_addgas ->
          let cost = (EVM.costl (to_evm instr)) in
          count i (BigInt.add gas cost) alloc label.label_index;
          count i (BigInt.add gas cost) alloc (pc+1)
      | instr ->
          let cost = (EVM.costl (to_evm instr)) in
          count i (BigInt.add gas cost) alloc (pc+1)
    in
    for pc=0 to Array.length asmmap - 1 do
      match asmmap.(pc) with
      | ADDGAS (Startgas i) ->
          count i BigInt.zero BigInt.zero (pc+1)
      | _ -> ()
    done

  let finalize l =
    linearize l;
    if Debug.test_flag gas_checking then
      gaz_checking l;
    let l = List.fold_left (fun acc e -> List.rev_append (to_evm e) acc) [] l in
    let l = List.rev l in
    l

end

module Print = struct

  open Mltree

  (* extraction attributes *)
  let external_attr = create_attribute "evm:external"
  let gas_checking_attr = create_attribute "evm:gas_checking"

  let is_external ~attrs =
    Sattr.mem external_attr attrs

  let is_gas_checking ~attrs =
    Sattr.mem gas_checking_attr attrs

  let get_constructors_from_constructor info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
        let eq_rs {itd_constructors} =
          List.exists (rs_equal rs) itd_constructors in
        (List.find eq_rs itdl).itd_constructors
    | _ -> assert false

  let get_tag_from_constructor info rs =
    let ctrs = get_constructors_from_constructor info rs in
    let tag = Lists.find_nth (fun rs' -> Expr.rs_equal rs rs') ctrs in
    tag

  let get_record_from_constructor info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
        let eq_rs {itd_constructors} =
          List.exists (rs_equal rs) itd_constructors in
        let itd = List.find eq_rs itdl in
        List.filter (fun e -> not (rs_ghost e)) itd.itd_fields
    | _ -> []

  let get_record_from_field info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
        let eq_rs {itd_fields} =
          List.exists (rs_equal rs) itd_fields in
        let itd = List.find eq_rs itdl in
        List.filter (fun e -> not (rs_ghost e)) itd.itd_fields
    | _ -> []

  let get_field_number_from_field info rs =
    let pjl = get_record_from_field info rs in
    let i = Lists.find_nth (fun rs' -> Expr.rs_equal rs rs') pjl in
    i

  (** Expressions *)

  let pv_name pv = pv.pv_vs.vs_name
  (* let print_pv info fmt pv = print_lident info fmt (pv_name pv) *)

  (* FIXME put these in Compile*)
  let is_true e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_true
    | _ -> false

  let is_false e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_false
    | _ -> false

  let is_unit = function
    | Ttuple [] -> true
    | _ -> false

  let removed_arg (_,ty,is_ghost) = is_ghost || is_unit ty

  let (!!) fmt = EVMSimple.copy_stack fmt

  let rec print_apply_args info (fmt:EVMSimple.stack) exprl =
      (** on the stack in reverse order *)
      Lists.iter_right (fun e -> print_expr info fmt e) exprl

  and print_apply info rs fmt pvl =
    let isfield =
      match rs.rs_field with
      | None   -> false
      | Some _ -> true in
    let isconstructor () =
      match Mid.find_opt rs.rs_name info.info_mo_known_map with
      | Some {pd_node = PDtype its} ->
          let is_constructor its =
            List.exists (rs_equal rs) its.itd_constructors in
          List.exists is_constructor its
      | _ -> false in
    match query_syntax info.info_syn rs.rs_name, pvl with
    | Some "add_gas", [{e_node=Econst g};{e_node=Econst a}] ->
        EVMSimple.add_gas fmt
          g.Number.il_int
          a.Number.il_int
    | Some "add_gas", _ ->
        invalid_arg "add_gas must have two constants as parameter"
    | Some "get_gas", [_] ->
        EVMSimple.add_auto fmt EVMSimple.GAS
    | Some "get_gas", _ ->
        invalid_arg "get_gas must have unit as parameter"
    | Some s, _ (* when is_local_id info rs.rs_name  *) ->
        let json = Json_base.get_list (Json_lexer.parse_json_object s) in
        print_apply_args info fmt pvl;
        List.iter (EVMSimple.add_auto_json fmt) json
    (* | None, [t] when is_rs_tuple rs -> *)
    (*     fprintf fmt "@[%a@]" (print_expr info) t *)
    (* | None, tl when is_rs_tuple rs -> *)
    (*     fprintf fmt "@[(%a)@]" (print_list comma (print_expr info)) tl *)
    | None, [t1] when isfield ->
        let i = get_field_number_from_field info rs in
        begin match t1.e_node with
          | Evar pvs when EVMSimple.is_global fmt pvs.Ity.pv_vs.vs_name ->
              let addr = EVMSimple.get_global_var fmt pvs.Ity.pv_vs.vs_name in
              EVMSimple.auto fmt EVMSimple.[
                  int_to_push (addr+32*i);
                  SLOAD;
                ]
          | _ ->
              print_expr info fmt t1;
              EVMSimple.auto fmt EVMSimple.[
                  int_to_push (32*i);
                  ADD;
                  MLOAD;
                ]
        end
    | None, tl when isconstructor () ->
        let pjl = get_record_from_constructor info rs in
        let store tag =
          let l = List.length tl in
          let size = (32 * l) in
          let size = match tag with None -> size | Some _ -> size + 32 in
          EVMSimple.Allocate.allocate fmt size;
          (** keep the base pointer *)
          begin match tag with
            | None ->
                EVMSimple.add_auto fmt EVMSimple.DUP1;
            | Some tag ->
                (** The tag could use MSTORE8 *)
                EVMSimple.auto fmt EVMSimple.[
                    int_to_push tag;
                    DUP2;
                    MSTORE;
                  ];
                if 0 < l then
                  EVMSimple.auto fmt EVMSimple.[
                      DUP1;
                      int_to_push 32;
                      ADD;
                    ];
          end;
          Lists.iteri (fun i e ->
              if 0 < i then
                EVMSimple.auto fmt EVMSimple.[
                    int_to_push 32;
                    ADD;
                  ];
              print_expr info fmt e;
              if i < l - 1
              then EVMSimple.add_auto fmt EVMSimple.DUP2
              else EVMSimple.add_auto fmt EVMSimple.SWAP1;
              EVMSimple.auto fmt EVMSimple.[
                  MSTORE;
                ]
            ) tl
        in
        begin match pjl with
          | [] -> (** Algebraic datatype *)
              let tag = get_tag_from_constructor info rs in
              store (Some tag)
          | _ ->
              store None
        end
    | _, tl ->
        let return = EVMSimple.new_label ~follow:false "call return" in
        EVMSimple.auto fmt EVMSimple.[
            PUSHLABEL return;
          ];
        let tl = List.filter (fun e -> not (Mltree.is_unit e.e_ity)) tl in
        print_apply_args info fmt tl;
        Debug.dprintf debug "CALL %s@." rs.rs_name.Ident.id_string;
        let call =
          match Expr.Mrs.find_opt rs fmt.EVMSimple.call_labels with
          | None -> invalid_arg (Format.sprintf "Unknown function: %s"
                                   rs.rs_name.Ident.id_string)
          | Some call -> call
        in
        EVMSimple.call fmt
          ~call
          ~return
          ~args:(List.length tl)
          ~ret:1 (*todo unit *)

  and print_def info fmt ~rs ~res ~args ~ef =
    let start_addgas, stop_addgas =
      if is_gas_checking ~attrs:rs.rs_name.id_attrs then
        let start, stop = EVMSimple.new_startstop_addgas () in
        [start],[stop]
      else [],[]
    in
    let fmt = { fmt with EVMSimple.bottom = fmt.EVMSimple.bottom } in
    let label = Expr.Mrs.find rs fmt.EVMSimple.call_labels in
    EVMSimple.auto fmt start_addgas;
    EVMSimple.jumpdest fmt label;
    let pushed = ref 0 in
    List.fold_right (fun ((v,_,_) as pv) () ->
        if removed_arg pv
        then ()
        else begin
          incr pushed;
          EVMSimple.add_arg fmt v
        end) args ();
    print_expr info fmt ef;
    (** put the result before all the popped elements and the return address *)
    if !pushed >= 1 && not (is_unit res) then
      EVMSimple.add_auto fmt (EVMSimple.swap (!pushed+1));
    List.fold_right (fun ((v,_,_) as pv) () ->
        if removed_arg pv
        then ()
        else EVMSimple.pop_var fmt v) args ();
    if not (is_unit res) then
      EVMSimple.add_auto fmt EVMSimple.SWAP1;
    EVMSimple.add_auto fmt EVMSimple.JUMPDYN;
    EVMSimple.auto fmt stop_addgas


  and print_let_def info fmt = function
    (* | Lvar (pv, e) -> *)
    (*     print_expr info fmt e; *)
    (*     fmt  *)
    (*     (pv_name pv) *)
    (*     fprintf fmt "@[<hov 2>let %a :=@ %a@]" *)
    (*       (print_lident info)  *)
    (*       (\* print_ity pv.pv_ity *\) *)
    | Lsym (rs, _, res, args, ef) ->
        print_def info fmt ~rs ~res ~args ~ef
    | Lrec rdef ->
        let print_one = function
          | { rec_sym = rs; rec_args = args; rec_exp = ef;
              rec_res = res; rec_svar = _ } ->
              print_def info fmt ~rs ~res ~args ~ef
        in
        List.iter print_one rdef
    (* | Lany (rs, _, res, []) when functor_arg -> *)
    (*     fprintf fmt "@[<hov 2>val %a : %a@]" *)
    (*       (print_lident info) rs.rs_name *)
    (*       (print_ty info) res; *)
    (* | Lany (rs, _, res, args) when functor_arg -> *)
    (*     let print_ty_arg info fmt (_, ty, _) = *)
    (*       fprintf fmt "@[%a@]" (print_ty info) ty in *)
    (*     fprintf fmt "@[<hov 2>val %a : @[%a@] ->@ %a@]" *)
    (*       (print_lident info) rs.rs_name *)
    (*       (print_list arrow (print_ty_arg info)) args *)
    (*       (print_ty info) res; *)
    (*     forget_vars args *)
  (* | Lany ({rs_name}, _, _, _) -> check_val_in_drv info rs_name.id_loc rs_name *)
    | _ -> ()(* invalid_arg "not_implemented_yet" *)

  and print_expr info (fmt:EVMSimple.stack) e : unit =
    let bot = fmt.EVMSimple.bottom in
    Debug.dprintf debug "expr:%a@." Mltree.print_expr e;
    begin match e.e_node with
      | Econst c ->
          let id = match e.e_ity with
            | I { ity_node = Ityapp ({its_ts = ts},_,_) } -> ts.ts_name
            | _ -> assert false
          in begin
            match query_syntax info.info_syn id with
            | Some "s32" | Some "u32"
            | Some "s64" | Some "u64"
            | Some "s128" | Some "u128"
            | Some "s256" | Some "u256" ->
                let i = c.Number.il_int in
                EVMSimple.add_auto fmt (EVMSimple.num_to_push i)
            | None ->
                invalid_arg (Format.sprintf "Unknown type: %s"
                               (BigInt.to_string c.Number.il_int))
            | Some s  ->
                invalid_arg (Format.sprintf "Unknown type: %s (%s)"
                               (BigInt.to_string c.Number.il_int) s)
          end
      | Evar pvs when Ity.ity_equal pvs.pv_ity Ity.ity_unit ->
          ()
      | Evar pvs ->
          begin match (EVMSimple.get_var fmt pvs.Ity.pv_vs.vs_name) with
            | `Local i ->
                let asm = EVMSimple.dup i in
                EVMSimple.add_auto fmt asm
            | `Global i ->
                EVMSimple.auto fmt EVMSimple.[
                    int_to_push i;
                    SLOAD;
                  ]
          end
      | Elet (Lvar(pv,e'), e) when Ity.ity_equal pv.pv_ity Ity.ity_unit ->
          print_expr info fmt e';
          print_expr info fmt e
      | Elet (Lvar(pv,e'), e) ->
          assert ( not (Mltree.is_unit e'.e_ity) );
          print_expr info fmt e';
          EVMSimple.bind_var fmt (pv_name pv);
          print_expr info fmt e;
          if not (Mltree.is_unit e.e_ity) then EVMSimple.add_auto fmt EVMSimple.SWAP1;
          EVMSimple.pop_var fmt (pv_name pv);
      | Elet (_, _) ->
          invalid_arg "unsupported local let def"
      | Eabsurd ->
          EVMSimple.add_auto fmt (EVMSimple.PUSH1 BigInt.zero)
      | Eapp (rs, []) when rs_equal rs rs_true ->
          EVMSimple.add_auto fmt (EVMSimple.PUSH1 BigInt.one)
      | Eapp (rs, []) when rs_equal rs rs_false ->
          EVMSimple.add_auto fmt (EVMSimple.PUSH1 BigInt.zero)
      | Eapp (rs, pvl) ->
          print_apply info rs fmt pvl
      (* | Ematch (e1, [p, e2], []) -> *)
      (*     fprintf fmt (protect_on paren "let %a =@ %a in@ %a") *)
      (*       (print_pat info) p (print_expr info) e1 (print_expr info) e2 *)
      (* | Ematch (e, pl, []) -> *)
      (*     fprintf fmt *)
      (*       (protect_on paren "begin match @[%a@] with@\n@[<hov>%a@]@\nend") *)
      (*       (print_expr info) e (print_list newline (print_branch info)) pl *)
      (* | Eassign al -> *)
      (*     let assign fmt (rho, rs, e) = *)
      (*       fprintf fmt "@[<hov 2>%a.%a <-@ %a@]" *)
      (*         (print_lident info) (pv_name rho) (print_lident info) rs.rs_name *)
      (*         (print_expr info) e in *)
      (*     begin match al with *)
      (*       | [] -> assert false | [a] -> assign fmt a *)
      (*       | al -> fprintf fmt "@[begin %a end@]" (print_list semi assign) al end *)
      | Eif (e1, e2, {e_node = Eblock []}) ->
          let lab = EVMSimple.new_label ~follow:true "ifnoelse" in
          print_expr info fmt e1;
          EVMSimple.add_auto fmt EVMSimple.NOT;
          EVMSimple.jumpi fmt lab;
          print_expr info fmt e2;
          EVMSimple.jumpdest fmt lab
      | Eif (e1, e2, e3) when is_false e2 && is_true e3 ->
          print_expr info fmt e1;
          EVMSimple.add_auto fmt EVMSimple.NOT
      | Eif (e1, e2, e3) ->
          let labthen = EVMSimple.new_label ~follow:true "ifthen" in
          let labend = EVMSimple.new_label  ~follow:true "ifend" in
          print_expr info fmt e1;
          EVMSimple.jumpi fmt labthen;
          print_expr info (!! fmt) e3;
          EVMSimple.jump fmt labend;
          EVMSimple.jumpdest fmt labthen;
          print_expr info fmt e2;
          EVMSimple.jumpdest fmt labend
      | Eblock [] -> () (* unit *)
      | Eblock [e] ->
          print_expr info fmt e
      | Eblock el ->
          List.iter (print_expr info fmt) el
      | Efun (_varl, _e) ->
          invalid_arg "unsupported Efun"
      | Ewhile (e1, e2) ->
          (** todo addgas handling *)
          let labstart = EVMSimple.new_label ~follow:false "whilestart" in
          let labtest = EVMSimple.new_label ~follow:true  "whiletest" in
          EVMSimple.jump fmt labtest;
          EVMSimple.jumpdest fmt labstart;
          print_expr info fmt e2;
          EVMSimple.jumpdest fmt labtest;
          print_expr info fmt e1;
          EVMSimple.jumpi fmt labstart;
      | Eraise (_, _) ->
          EVMSimple.auto fmt EVMSimple.[
              PUSH1 BigInt.zero;
              DUP1;
              REVERT;
            ];
          (** not executed but for the invariants *)
          if not (Mltree.is_unit e.e_ity) then EVMSimple.add_auto fmt EVMSimple.DUP1
      (* | Efor (pv1, pv2, dir, pv3, e) -> *)
      (*     if is_mapped_to_int info pv1.pv_ity then begin *)
      (*       fprintf fmt "@[<hov 2>for %a = %a %a %a do@ @[%a@]@ done@]" *)
      (*         (print_lident info) (pv_name pv1) (print_lident info) (pv_name pv2) *)
      (*         print_for_direction dir (print_lident info) (pv_name pv3) *)
      (*         (print_expr info) e; *)
      (*       forget_pv pv1 end *)
      (*     else *)
      (*       let for_id  = id_register (id_fresh "for_loop_to") in *)
      (*       let cmp, op = match dir with *)
      (*         | To     -> "Z.leq", "Z.succ" *)
      (*         | DownTo -> "Z.geq", "Z.pred" in *)
      (*       fprintf fmt (protect_on paren *)
      (*                      "@[<hov 2>let rec %a %a =@ if %s %a %a then \ *)
                              (*                       begin@ %a; %a (%s %a) end@ in@ %a %a@]") *)
      (*       (\* let rec *\) (print_lident info) for_id (print_pv info) pv1 *)
      (*       (\* if      *\)  cmp (print_pv info) pv1 (print_pv info) pv3 *)
      (*       (\* then    *\) (print_expr info) e (print_lident info) for_id *)
      (*                     op (print_pv info) pv1 *)
      (*       (\* in      *\) (print_lident info) for_id (print_pv info) pv2 *)
      | Ematch (e, bl, []) ->
          let bot = fmt.EVMSimple.bottom in
          let after = EVMSimple.new_label ~follow:true "after" in
          let bl = List.map (fun (pat,e) -> (pat,e,EVMSimple.new_label ~follow:true "branch")) bl in
          print_expr info fmt e;
          EVMSimple.auto fmt EVMSimple.[
              DUP1;
              MLOAD;
            ];
          let last = List.length bl - 1 in
          let iter_pat i (pat,_,lab) =
            match pat with
            | Pwild ->
                EVMSimple.auto fmt EVMSimple.[
                    JUMP lab;
                  ]
            | Papp(ls,_) ->
                if i = last then
                  EVMSimple.auto fmt EVMSimple.[
                      JUMP lab;
                    ]
                else
                  let rs = restore_rs ls in
                  let tag = get_tag_from_constructor info rs in
                  EVMSimple.auto fmt EVMSimple.[
                      DUP1;
                      int_to_push tag;
                      EQ;
                      JUMPI lab;
                    ]
            | _ -> invalid_arg "unsupported pattern"
          in
          List.iteri iter_pat bl;
          let iter_branch (pat,e,lab) =
            let fmt = { fmt with EVMSimple.bottom = fmt.EVMSimple.bottom } in
            EVMSimple.auto fmt EVMSimple.[
                JUMPDEST lab;
                POP;
              ];
            begin
              match pat with
              | Pwild -> ()
              | Papp(ls,bindings) ->
                  let bot = fmt.EVMSimple.bottom in
                  let rs = restore_rs ls in
                  let is_record = get_record_from_constructor info rs <> [] in
                  let bind i = function
                    | Pwild -> ()
                    | Pvar v ->
                        EVMSimple.auto fmt EVMSimple.[
                            DUP1;
                            int_to_push (32*i + (if is_record then 0 else 32));
                            ADD;
                            MLOAD;
                          ];
                        EVMSimple.bind_var fmt v.vs_name
                    | _ -> invalid_arg "unsupported deep pattern"
                  in
                  Lists.iteri bind bindings;
                  print_expr info fmt e;
                  let pop = function
                    | Pwild -> ()
                    | Pvar v ->
                        if not (Mltree.is_unit e.e_ity) then EVMSimple.add_auto fmt EVMSimple.SWAP1;
                        EVMSimple.pop_var fmt v.vs_name
                    | _ -> invalid_arg "unsupported deep pattern"
                  in
                  List.iter pop bindings;
                  let bot' = fmt.EVMSimple.bottom in
                  assert ( bot+(if (Mltree.is_unit e.e_ity) then 0 else 1) = bot' )
              | _ -> assert false;
            end;
            EVMSimple.jump fmt after
          in
          List.iter iter_branch bl;
          EVMSimple.auto fmt EVMSimple.[
              JUMPDEST after;
              SWAP1;
              POP;
            ];
          let bot' = fmt.EVMSimple.bottom in
          assert ( bot+1 = bot' )
      | Ematch (_, _, _) ->
          invalid_arg "match with exception not supported"
      (* | Eexn (xs, None, e) -> *)
      (*     fprintf fmt "@[<hv>let exception %a in@\n%a@]" *)
      (*       (print_uident info) xs.xs_name (print_expr info) e *)
      (* | Eexn (xs, Some t, e) -> *)
      (*     fprintf fmt "@[<hv>let exception %a of %a in@\n%a@]" *)
      (*       (print_uident info) xs.xs_name (print_ty ~paren:true info) t *)
      (*       (print_expr info) e *)
      | Eignore e ->
          print_expr info fmt e;
          EVMSimple.add_auto fmt EVMSimple.POP
      | Eassign al ->
          let assign (rho, rs, e) =
            let v = pv_name rho in
            print_expr info fmt e;
            let i = get_field_number_from_field info rs in
            match EVMSimple.get_var fmt v with
            | `Local addr ->
                EVMSimple.auto fmt EVMSimple.[
                    dup addr;
                    int_to_push (32*i);
                    ADD;
                    MSTORE;
                  ]
            | `Global addr ->
                EVMSimple.auto fmt EVMSimple.[
                    int_to_push (addr+32*i);
                    SSTORE;
                  ]
          in
          List.iter assign al
    | _ ->
        invalid_arg (Pp.sprintf "Unsupported expression: %a" Mltree.print_expr e)
    end;
    Debug.dprintf debug "%i %i(%b):%a@." bot fmt.EVMSimple.bottom (Mltree.is_unit e.e_ity) Mltree.print_expr e;
    assert (bot + (if Mltree.is_unit e.e_ity then 0 else 1) = fmt.EVMSimple.bottom)

  (* and print_branch info fmt (p, e) = *)
  (*   fprintf fmt "@[<hov 2>| %a ->@ @[%a@]@]" *)
  (*     (print_pat info) p (print_expr info) e; *)
  (*   forget_pat p *)

  (* and print_raise ~paren info xs fmt e_opt = *)
  (*   match query_syntax info.info_syn xs.xs_name, e_opt with *)
  (*   | Some s, None -> *)
  (*       fprintf fmt "raise (%s)" s *)
  (*   | Some s, Some e -> *)
  (*       fprintf fmt (protect_on paren "raise (%a)") *)
  (*         (syntax_arguments s (print_expr info)) [e] *)
  (*   | None, None -> *)
  (*       fprintf fmt (protect_on paren "raise %a") *)
  (*         (print_uident info) xs.xs_name *)
  (*   | None, Some e -> *)
  (*       fprintf fmt (protect_on paren "raise (%a %a)") *)
  (*         (print_uident info) xs.xs_name (print_expr ~paren:true info) e *)

  (* and print_xbranch info case fmt (xs, pvl, e) = *)
  (*   let print_exn fmt () = *)
  (*     if case then fprintf fmt "exception " else fprintf fmt "" in *)
  (*   let print_var fmt pv = print_lident info fmt (pv_name pv) in *)
  (*   match query_syntax info.info_syn xs.xs_name, pvl with *)
  (*   | Some s, _ -> fprintf fmt "@[<hov 4>| %a%a ->@ %a@]" *)
  (*       print_exn () (syntax_arguments s print_var) pvl *)
  (*       (print_expr info ~paren:true) e *)
  (*   | None, [] -> fprintf fmt "@[<hov 4>| %a%a ->@ %a@]" *)
  (*       print_exn () (print_uident info) xs.xs_name (print_expr info) e *)
  (*   | None, [pv] -> fprintf fmt "@[<hov 4>| %a%a %a ->@ %a@]" *)
  (*       print_exn () (print_uident info) xs.xs_name print_var pv *)
  (*       (print_expr info) e *)
  (*   | None, pvl -> fprintf fmt "@[<hov 4>| %a%a (%a) ->@ %a@]" *)
  (*       print_exn () (print_uident info) xs.xs_name *)
  (*       (print_list comma print_var) pvl (print_expr info) e *)

  let print_decl info fmt = function
    | Dlet ldef ->
        print_let_def info fmt ldef
    (* | Dval (pv, ty) -> *)
    (*     print_top_val info ~functor_arg fmt (pv, ty) *)
    (* | Dtype dl -> *)
    (*     print_list_next newline (print_type_decl info) fmt dl *)
    (* | Dexn (xs, None) -> *)
    (*     fprintf fmt "exception %a" (print_uident info) xs.xs_name *)
    (* | Dexn (xs, Some t)-> *)
    (*     fprintf fmt "@[<hov 2>exception %a of %a@]" *)
    (*       (print_uident info) xs.xs_name (print_ty ~paren:true info) t *)
    (* | Dmodule (s, dl) -> *)
    (*     let args, dl = extract_functor_args info dl in *)
    (*     let info = { info with info_current_ph = s :: info.info_current_ph } in *)
    (*     fprintf fmt "@[@[<hov 2>module %s%a@ =@]@\n@[<hov 2>struct@ %a@]@ end" s *)
    (*       (print_functor_args info) args *)
    (*       (print_list newline2 (print_decl info)) dl *)
    | _ -> ()

  (* and print_functor_args info fmt args = *)
  (*   let print_sig info fmt dl = *)
  (*     fprintf fmt "sig@ %a@ end" *)
  (*       (print_list newline (print_decl info ~functor_arg:true)) dl in *)
  (*   let print_pair fmt (s, dl) = *)
  (*     let info = { info with info_current_ph = s :: info.info_current_ph } in *)
  (*     fprintf fmt "(%s:@ %a)" s (print_sig info) dl in *)
  (*   fprintf fmt "%a" (print_list space print_pair) args *)

  let print_decl info fmt decl =
    (* avoids printing the same decl for mutually recursive decls *)
    let memo = Hashtbl.create 64 in
    let decl_name = get_decl_name decl in
    let decide_print id =
      if query_syntax info.info_syn id = None &&
         not (Hashtbl.mem memo decl) then begin
        Hashtbl.add memo decl ();
        print_decl info fmt decl;
      end in
    List.iter decide_print decl_name

end

let print_decl =
  let memo = Hashtbl.create 16 in
  fun pargs fmt (({mod_theory = th} as m),d) ->
    let info = {
      info_syn          = pargs.Pdriver.syntax;
      info_literal      = pargs.Pdriver.literal;
      info_current_th   = th;
      info_current_mo   = Some m;
      info_th_known_map = th.th_known;
      info_mo_known_map = m.mod_known;
      info_fname        = None;
      info_flat         = true;
      info_current_ph   = [];
    } in
    if not (Hashtbl.mem memo d) then begin Hashtbl.add memo d ();
      Print.print_decl info fmt d end

let print_decls pargs fmt l =
  let next_globals = ref 1 in
  let label_function_aux (labels, externals, globals) ~rs ~res ~args =
    match args with
    | [] ->
        let globals = Mid.add rs.rs_name !next_globals globals in
        incr next_globals;
        (labels, externals, globals)
    | _ ->
        let externals =
          if Print.is_external ~attrs:rs.rs_name.id_attrs
          then
            let ty_args = Lists.map_filter (fun ((_, ty, _) as arg) ->
                if Print.removed_arg arg then None else Some ty) args in
            let label_arg_extraction = EVMSimple.new_label ~follow:true "arg_extract" in
            (rs,ty_args,res,label_arg_extraction)::externals
          else externals
        in
        let label = EVMSimple.new_label ~follow:false (Pp.sprintf "Lsym:%s" rs.rs_name.Ident.id_string) in
        let labels = Expr.Mrs.add rs label labels in
        labels,externals,globals
  in
  let label_function ((labels, externals, globals) as acc) (_,d) =
    match d with
    | Mltree.Dlet (Mltree.Lvar (pv,_)) ->
        let globals = Mid.add (Print.pv_name pv) !next_globals globals in
        incr next_globals;
        (labels, externals, globals)
    | Mltree.Dlet (Mltree.Lsym (rs, _, res, args, _)) ->
        label_function_aux acc ~rs ~res ~args
    | Mltree.Dlet (Mltree.Lrec rdef) ->
        let print_one acc = function
          | { Mltree.rec_sym = rs; rec_args = args; rec_exp = _;
              rec_res = res; rec_svar = _ } ->
              label_function_aux acc ~rs ~res ~args
        in
        List.fold_left print_one acc rdef
    | Mltree.Dtype _ | Mltree.Dexn _ -> acc
    | Mltree.Dmodule (_,_) -> invalid_arg "unsupported module"
    | _ ->  invalid_arg "unsupported decl"
  in
  let (labels, externals,globals) =
    List.fold_left label_function (Expr.Mrs.empty, [], Ident.Mid.empty) l
  in
  let stack = {
    EVMSimple.asm = { EVMSimple.codes = [] };
    local = Ident.Mid.empty;
    global = globals;
    bottom = 0;
    call_labels = labels;
  } in

  (** init *)
  let label_revert = EVMSimple.new_label ~follow:true "revert" in
  EVMSimple.Allocate.init stack;
  EVMSimple.auto stack
    [EVMSimple.PUSH1 (BigInt.of_int 0x04);
     EVMSimple.CALLDATASIZE;
     EVMSimple.LT;
     EVMSimple.JUMPI label_revert;
    ];
  EVMSimple.auto stack
    EVMSimple.[num_to_push (BigInt.pow_int_pos 2 0xe0);
               PUSH1 BigInt.zero;
               CALLDATALOAD;
               DIV;
              ];

  (** dispatch *)
  let dispatch (rs,_,_,label_arg_extraction) =
    (* 0x0a9a2963 for "f(int8)" *)
    let i =
      Cryptokit.hash_string (Cryptokit.Hash.keccak 256)
        rs.rs_name.Ident.id_string in
    let f j = BigInt.mul
        (BigInt.of_int (Char.code i.[j]))
        (BigInt.pow_int_pos 256 (3-j))
    in
    let hashname =
      List.fold_left BigInt.add BigInt.zero
        [f 0;f 1;f 2 ;f 3]
    in
    Format.eprintf "For function %s hashname %x@."
      rs.rs_name.Ident.id_string (BigInt.to_int hashname);
    EVMSimple.auto stack
      EVMSimple.[DUP1;
                 PUSH4 hashname;
                 EQ;
                 JUMPI label_arg_extraction
                ];
  in
  List.iter dispatch externals;

  EVMSimple.auto stack
    EVMSimple.[JUMPDEST label_revert;
               PUSH1 BigInt.zero;
               DUP1;
               REVERT];
  EVMSimple.Allocate.define_allocate stack;

  (** label extraction *)
  let arg_extraction (rs,args,_,label_arg_extraction) =
    let stack = EVMSimple.copy_stack stack in
    let size ty =
      let id = match ty with
        | Mltree.Tapp (id,[]) -> id
        | _ -> invalid_arg "Unknown type arg_extraction"
      in
      match query_syntax pargs.Pdriver.syntax id with
        | Some "s32" | Some "u32"
        | Some "s64" | Some "u64"
        | Some "s128" | Some "u128"
        | Some "s256" | Some "u256" -> ()
        | None | Some _  ->
            invalid_arg "Unknown type arg_extraction"
    in
    List.iter size args;
    let args_size = 32 * List.length args in
    let datasize = args_size + 0x04 in

    let label_ret_encoding = EVMSimple.new_label ~follow:false "ret_encoding" in

    EVMSimple.jumpdest stack label_arg_extraction;
    EVMSimple.auto stack EVMSimple.[
        POP; (** previous function identifier *)
        int_to_push datasize;
        CALLDATASIZE;
        LT;
        JUMPI label_revert;
        PUSHLABEL label_ret_encoding;
      ];
    let get_args offset _ =
      EVMSimple.auto stack [
        EVMSimple.int_to_push offset;
        EVMSimple.CALLDATALOAD;
      ];
      offset+32
    in
    let _ = List.fold_left get_args 0x04 args in
    EVMSimple.auto stack EVMSimple.[
      JUMP (Expr.Mrs.find rs labels);
      JUMPDEST label_ret_encoding;
    ];
    EVMSimple.Allocate.allocate stack 0x20;
    EVMSimple.auto stack EVMSimple.[
        SWAP1;
        DUP2;
        MSTORE;
        EVMSimple.int_to_push 0x20;
        SWAP1;
        RETURN;
      ]
  in
  List.iter arg_extraction externals;

  List.iter (print_decl pargs stack) l;
  let asms = EVMSimple.finalize (List.rev stack.EVMSimple.asm.EVMSimple.codes) in
  Debug.dprintf debug "%a@." EVM.print_humanl asms;
  EVM.print_code fmt asms

  (* let label = { EVMSimple.label_name = "jump"; EVMSimple.label_addr = BigInt.zero } in *)
  (* let l = let open EVMSimple in *)
  (*   [ *)
  (*     JUMP label; *)
  (*     PUSH1 (BigInt.of_int 0x42); *)
  (*     PUSH1 (BigInt.of_int 0x80); *)
  (*     MSTORE; *)
  (*     JUMPDEST label; *)
  (*     PUSH1 (BigInt.of_int 0x20); *)
  (*     PUSH1 (BigInt.of_int 0x80); *)
  (*     RETURN; *)
  (*   ] *)
  (* in *)


let ng suffix ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  (module_name ?fname path mod_name) ^ suffix

let file_gen = ng ".evm"

open Pdriver

let yul_printer =
  { desc_only_flat      = "printer for EVM code";
    file_gen_only_flat  = file_gen;
    decls_printer_only_flat = print_decls;
  }

let () = Pdriver.register_printer_only_flat "evm" yul_printer


(**

let i = (Cryptokit.hash_string (Cryptokit.Hash.keccak 256) "g(uint256)");;
let f j = Int32.shift_left (Int32.of_int (Char.code i.[j])) j;;

*)
