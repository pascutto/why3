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

(** Printer for extracted Yul code *)

(** Currently we target strict-assembly instead of Yul,
    because it is not mature enough. For example built-in functions
    are not defined.
*)

(** From https://solidity.readthedocs.io/en/latest/assembly.html
    ethereum Revision cc4d30a7

AssemblyBlock = '{' AssemblyItem* '}'
AssemblyItem =
    Identifier |
    AssemblyBlock |
    AssemblyExpression |
    AssemblyLocalDefinition |
    AssemblyAssignment |
    AssemblyStackAssignment |
    LabelDefinition |
    AssemblyIf |
    AssemblySwitch |
    AssemblyFunctionDefinition |
    AssemblyFor |
    'break' |
    'continue' |
    SubAssembly
AssemblyExpression = AssemblyCall | Identifier | AssemblyLiteral
AssemblyLiteral = NumberLiteral | StringLiteral | HexLiteral
Identifier = [a-zA-Z_$] [a-zA-Z_0-9]*
AssemblyCall = Identifier '(' ( AssemblyExpression ( ',' AssemblyExpression )* )? ')'
AssemblyLocalDefinition = 'let' IdentifierOrList ( ':=' AssemblyExpression )?
AssemblyAssignment = IdentifierOrList ':=' AssemblyExpression
IdentifierOrList = Identifier | '(' IdentifierList ')'
IdentifierList = Identifier ( ',' Identifier)*
AssemblyStackAssignment = '=:' Identifier
LabelDefinition = Identifier ':'
AssemblyIf = 'if' AssemblyExpression AssemblyBlock
AssemblySwitch = 'switch' AssemblyExpression AssemblyCase*
    ( 'default' AssemblyBlock )?
AssemblyCase = 'case' AssemblyExpression AssemblyBlock
AssemblyFunctionDefinition = 'function' Identifier '(' IdentifierList? ')'
    ( '->' '(' IdentifierList ')' )? AssemblyBlock
AssemblyFor = 'for' ( AssemblyBlock | AssemblyExpression )
    AssemblyExpression ( AssemblyBlock | AssemblyExpression ) AssemblyBlock
SubAssembly = 'assembly' Identifier AssemblyBlock
NumberLiteral = HexNumber | DecimalNumber
HexLiteral = 'hex' ('"' ([0-9a-fA-F]{2})* '"' | '\'' ([0-9a-fA-F]{2})* '\'')
StringLiteral = '"' ([^"\r\n\\] | '\\' .)* '"'
HexNumber = '0x' [0-9a-fA-F]+
DecimalNumber = [0-9]+

*)

open Compile
open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Wstdlib
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

type price =
  | PriceZero
  | PriceVeryLow
  | PriceLow
  | PriceMid
  | PriceHigh
  | PriceSpecial
  | PriceBase
  | PriceExtCode
  | PriceExt
  | PriceBalance

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
  | SUB -> { name = "SUB"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceVeryLow; code = 0x02; }
  | MUL -> { name = "MUL"; pushed = 0; args = 2; ret = 1; sideeffects = false; price = PriceLow; code = 0x03; }
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
  | SLOAD -> { name = "SLOAD"; pushed = 0; args = 1; ret = 1; sideeffects = false; price = PriceSpecial; code = 0x54; }
  | SSTORE -> { name = "SSTORE"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceSpecial; code = 0x55; }
  | JUMP -> { name = "JUMP"; pushed = 0; args = 1; ret = 0; sideeffects = true; price = PriceMid; code = 0x56; }
  | JUMPI -> { name = "JUMPI"; pushed = 0; args = 2; ret = 0; sideeffects = true; price = PriceHigh; code = 0x57; }
  | PC -> { name =  "PC"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x58; }
  | MSIZE -> { name = "MSIZE"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x59; }
  | GAS -> { name = "GAS"; pushed = 0; args = 0; ret = 1; sideeffects = false; price = PriceBase; code = 0x5a; }
  | JUMPDEST -> { name = "JUMPDEST"; pushed = 0; args = 0; ret = 0; sideeffects = true; price = PriceSpecial; code = 0x5b; }
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

end

module EVMSimple = struct

  type label = {
    label_name: string;
    mutable label_addr: int option;
    (** set once all the code is known *)
  }

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
   | JUMPI of label
   | PC
   | MSIZE
   | GAS
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

  type asm = {
    codes: instruction Queue.t;
  }

  type stack = {
    asm: asm;
    stack: int Ity.Mpv.t;
    mutable bottom: int;
  }

  let add stack asm popped pushed =
    Queue.add asm stack.asm.codes;
    stack.bottom <- stack.bottom - popped + pushed

  let add_var stack var =
    let stack = { stack with stack = Ity.Mpv.add var stack.bottom stack.stack } in
    stack

  let get_var stack var =
    Ity.Mpv.find var stack.stack

end

open EVMSimple

module Print = struct

  open Mltree

  (* extraction attributes *)
  let optional_arg = create_attribute "yul:optional"
  let named_arg = create_attribute "yul:named"
  let yul_remove = create_attribute "yul:remove"

  let is_optional ~attrs =
    Sattr.mem optional_arg attrs

  let is_named ~attrs =
    Sattr.mem named_arg attrs

  let is_yul_remove ~attrs =
    Ident.Sattr.mem yul_remove attrs

  let yul_keywords =
    ["function"; "default"; "if"; "switch"; "case"; "default"; "for"; "break"; "continue"; "bool";
     "u8"; "u32"; "u64"; "u128"; "u256"; "s8"; "s32"; "s64"; "s128"; "s256";
     "true"; "false";
     "result";
    ]

  let _is_yul_keyword =
    let h = Hstr.create 16 in
    List.iter (fun s -> Hstr.add h s ()) yul_keywords;
    Hstr.mem h

  (* iprinter: local names
     aprinter: type variables
     tprinter: toplevel definitions *)
  let iprinter, aprinter, tprinter =
    let isanitize = sanitizer char_to_alnumus char_to_alnumus in
    let lsanitize = sanitizer char_to_lalnumus char_to_alnumus in
    create_ident_printer yul_keywords ~sanitizer:isanitize,
    create_ident_printer yul_keywords ~sanitizer:lsanitize,
    create_ident_printer yul_keywords ~sanitizer:lsanitize

  let forget_id id = forget_id iprinter id
  let _forget_ids = List.iter forget_id
  let forget_var (id, _, _) = forget_id id
  let forget_vars = List.iter forget_var

  let forget_let_defn = function
    | Lvar (v,_) -> forget_id v.pv_vs.vs_name
    | Lsym (s,_,_,_) | Lany (s,_,_) -> forget_rs s
    | Lrec rdl -> List.iter (fun fd -> forget_rs fd.rec_sym) rdl

  let rec forget_pat = function
    | Pwild -> ()
    | Pvar {vs_name=id} -> forget_id id
    | Papp (_, pl) | Ptuple pl -> List.iter forget_pat pl
    | Por (p1, p2) -> forget_pat p1; forget_pat p2
    | Pas (p, _) -> forget_pat p

  let print_global_ident ~sanitizer fmt id =
    let s = id_unique ~sanitizer tprinter id in
    Ident.forget_id tprinter id;
    fprintf fmt "%s" s

  let print_path ~sanitizer fmt (q, id) =
    assert (List.length q >= 1);
    match Lists.chop_last q with
    | [], _ -> print_global_ident ~sanitizer fmt id
    | q, _  ->
        fprintf fmt "%a.%a"
          (print_list dot string) q (print_global_ident ~sanitizer) id

  let rec remove_prefix acc current_path = match acc, current_path with
    | [], _ | _, [] -> acc
    | p1 :: _, p2 :: _ when p1 <> p2 -> acc
    | _ :: r1, _ :: r2 -> remove_prefix r1 r2

  let is_local_id info id =
    Sid.mem id info.info_current_th.th_local ||
    Opt.fold (fun _ m -> Sid.mem id m.Pmodule.mod_local)
      false info.info_current_mo

  exception Local

  let print_qident ~sanitizer info fmt id =
    try
      if info.info_flat then raise Not_found;
      if is_local_id info id then raise Local;
      let p, t, q =
        try Pmodule.restore_path id with Not_found -> Theory.restore_path id in
      let fname = if p = [] then info.info_fname else None in
      let m = Strings.capitalize (module_name ?fname p t) in
      fprintf fmt "%s.%a" m (print_path ~sanitizer) (q, id)
    with
    | Not_found ->
        let s = id_unique ~sanitizer iprinter id in
        fprintf fmt "%s" s
    | Local ->
        let _, _, q =
          try Pmodule.restore_path id with Not_found ->
            Theory.restore_path id in
        let q = remove_prefix q (List.rev info.info_current_ph) in
        print_path ~sanitizer fmt (q, id)

  let print_lident = print_qident ~sanitizer:Strings.uncapitalize
  let print_uident = print_qident ~sanitizer:Strings.capitalize

  let print_tv fmt tv =
    fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

  let protect_on b s =
    if b then "(" ^^ s ^^ ")" else s

  let star fmt () = fprintf fmt " *@ "

  let rec print_list2 sep sep_m print1 print2 fmt (l1, l2) =
    match l1, l2 with
    | [x1], [x2] ->
        print1 fmt x1; sep_m fmt (); print2 fmt x2
    | x1 :: r1, x2 :: r2 ->
        print1 fmt x1; sep_m fmt (); print2 fmt x2; sep fmt ();
        print_list2 sep sep_m print1 print2 fmt (r1, r2)
    | _ -> ()

  let print_rs info fmt rs =
    fprintf fmt "%a" (print_lident info) rs.rs_name

  (** Types *)

  let rec print_ty ?(paren=false) info fmt = function
    | Tvar tv ->
        print_tv fmt tv
    | Ttuple [] ->
        fprintf fmt "unit"
    | Ttuple [t] ->
        print_ty ~paren info fmt t
    | Ttuple tl ->
        fprintf fmt (protect_on paren "@[%a@]")
          (print_list star (print_ty ~paren:true info)) tl
    | Tapp (ts, tl) ->
        match query_syntax info.info_syn ts with
        | Some s ->
            fprintf fmt (protect_on paren "%a")
              (syntax_arguments s (print_ty ~paren:true info)) tl
        | None   ->
            match tl with
            | [] ->
                (print_lident info) fmt ts
            | [ty] ->
                fprintf fmt (protect_on paren "%a@ %a")
                  (print_ty ~paren:true info) ty (print_lident info) ts
            | tl ->
                fprintf fmt (protect_on paren "(%a)@ %a")
                  (print_list comma (print_ty ~paren:false info)) tl
                  (print_lident info) ts

  let print_vsty_opt info fmt id ty =
    fprintf fmt "?%s:(%a:@ %a)" id.id_string (print_lident info) id
      (print_ty ~paren:false info) ty

  let print_vsty_named info fmt id ty =
    fprintf fmt "~%s:(%a:@ %a)" id.id_string (print_lident info) id
      (print_ty ~paren:false info) ty

  let print_vsty info fmt (id, ty, _) =
    let attrs = id.id_attrs in
    if is_optional ~attrs then print_vsty_opt info fmt id ty
    else if is_named ~attrs then print_vsty_named info fmt id ty
    else fprintf fmt "%a" (print_lident info) id
        (* (print_ty ~paren:false info) ty *)

  let print_tv_arg = print_tv
  let print_tv_args fmt = function
    | []   -> ()
    | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
    | tvl  -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

  let print_vs_arg info fmt vs =
    fprintf fmt "@[%a@]" (print_vsty info) vs

  let get_record info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
        let eq_rs {itd_constructors} =
          List.exists (rs_equal rs) itd_constructors in
        let itd = List.find eq_rs itdl in
        List.filter (fun e -> not (rs_ghost e)) itd.itd_fields
    | _ -> []

  let rec print_pat ?(paren=false) info fmt = function
    | Pwild ->
        fprintf fmt "$wild"
    | Pvar {vs_name=id} ->
        (print_lident info) fmt id
    | Pas (p, {vs_name=id}) ->
        fprintf fmt (protect_on paren "%a as %a") (print_pat info) p
          (print_lident info) id
    | Por (p1, p2) ->
        fprintf fmt (protect_on paren "%a | %a") (print_pat info) p1
          (print_pat info) p2
    | Ptuple pl ->
        fprintf fmt "(%a)" (print_list comma (print_pat ~paren:true info)) pl
    | Papp (ls, pl) ->
        match query_syntax info.info_syn ls.ls_name, pl with
        | Some s, _ ->
            syntax_arguments s (print_pat info) fmt pl
        | None, pl ->
            let pjl = let rs = restore_rs ls in get_record info rs in
            match pjl with
            | []  -> print_papp info ls fmt pl
            | pjl ->
                fprintf fmt (protect_on paren "@[<hov 2>{ %a }@]")
                  (print_list2 semi equal (print_rs info)
                  (print_pat ~paren: true info)) (pjl, pl)

  and print_papp info ls fmt = function
    | []  -> fprintf fmt "%a"      (print_uident info) ls.ls_name
    | [p] -> fprintf fmt "%a %a"   (print_uident info) ls.ls_name
               (print_pat info) p
    | pl  -> fprintf fmt "%a (%a)" (print_uident info) ls.ls_name
               (print_list comma (print_pat info)) pl

  (** Expressions *)

  let pv_name pv = pv.pv_vs.vs_name
  let print_pv info fmt pv = print_lident info fmt (pv_name pv)

  (* FIXME put these in Compile*)
  let is_true e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_true
    | _ -> false

  let is_false e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_false
    | _ -> false

  let check_val_in_drv info loc id =
    (* here [rs] refers to a [val] declaration *)
    match query_syntax info.info_syn id with
    | None (* when info.info_flat *) ->
        Loc.errorm ?loc "Symbol %a cannot be extracted" (print_lident info) id
    | _ -> ()

  let is_mapped_to_int info ity =
    match ity.ity_node with
    | Ityapp ({ its_ts = ts }, _, _) ->
        query_syntax info.info_syn ts.ts_name = Some "int"
    | _ -> false

  let print_constant fmt e = begin match e.e_node with
    | Econst c ->
        let s = BigInt.to_string (Number.compute_int_constant c) in
        if c.Number.ic_negative then fprintf fmt "(%s)" s
        else fprintf fmt "%s" s
    | _ -> assert false end

  let print_for_direction fmt = function
    | To     -> fprintf fmt "to"
    | DownTo -> fprintf fmt "downto"

  let rec print_apply_args info fmt = function
    | expr :: exprl, pv :: pvl ->
        if is_optional ~attrs:(pv_name pv).id_attrs then
          begin match expr.e_node with
            | Eapp (rs, _)
              when query_syntax info.info_syn rs.rs_name = Some "None" -> ()
            | _ -> fprintf fmt "?%s:%a" (pv_name pv).id_string
                     (print_expr ~paren:true info) expr end
        else if is_named ~attrs:(pv_name pv).id_attrs then
          fprintf fmt "~%s:%a" (pv_name pv).id_string
            (print_expr ~paren:true info) expr
        else fprintf fmt "%a" (print_expr ~paren:true info) expr;
        if exprl <> [] then fprintf fmt "@ ";
        print_apply_args info fmt (exprl, pvl)
    | expr :: exprl, [] ->
        fprintf fmt "%a" (print_expr ~paren:true info) expr;
        print_apply_args info fmt (exprl, [])
    | [], _ -> ()

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
    | Some s, _ (* when is_local_id info rs.rs_name  *)->
        syntax_arguments s (print_expr ~paren:true info) fmt pvl;
    | None, [t] when is_rs_tuple rs ->
        fprintf fmt "@[%a@]" (print_expr info) t
    | None, tl when is_rs_tuple rs ->
        fprintf fmt "@[(%a)@]" (print_list comma (print_expr info)) tl
    | None, [t1] when isfield ->
        fprintf fmt "%a.%a" (print_expr info) t1 (print_lident info) rs.rs_name
    | None, tl when isconstructor () ->
        let pjl = get_record info rs in
        begin match pjl, tl with
          | [], [] ->
              (print_uident info) fmt rs.rs_name
          | [], [t] ->
              fprintf fmt "@[<hov 2>%a %a@]" (print_uident info) rs.rs_name
                (print_expr ~paren:true info) t
          | [], tl ->
              fprintf fmt "@[<hov 2>%a (%a)@]" (print_uident info) rs.rs_name
                (print_list comma (print_expr ~paren:true info)) tl
          | pjl, tl -> let equal fmt () = fprintf fmt " =@ " in
              fprintf fmt "@[<hov 2>{ %a }@]"
                (print_list2 semi equal (print_rs info)
                   (print_expr ~paren:true info)) (pjl, tl) end
    | None, [] ->
        (print_lident info) fmt rs.rs_name
    | _, tl ->
        fprintf fmt "@[<hov 2>%a %a@]"
          (print_lident info) rs.rs_name
          (print_apply_args info) (tl, rs.rs_cty.cty_args)
  (* (print_list space (print_expr ~paren:true info)) tl *)

  and print_svar fmt s =
    Stv.iter (fun tv -> fprintf fmt "%a " print_tv tv) s

  and print_fun_type_args info fmt (args, s, res, e) =
    if Stv.is_empty s then
      fprintf fmt "@[%a@] :@ %a@ =@ %a"
        (print_list space (print_vs_arg info)) args
        (print_ty info) res
        (print_expr info) e
    else
      let ty_args = List.map (fun (_, ty, _) -> ty) args in
      let id_args = List.map (fun (id, _, _) -> id) args in
      let arrow fmt () = fprintf fmt " ->@ " in
      fprintf fmt ":@ @[<h>@[%a@]. @[%a ->@ %a@]@] =@ \
                   @[<hov 2>fun @[%a@]@ ->@ %a@]"
        print_svar s
        (print_list arrow (print_ty ~paren:true info)) ty_args
        (print_ty ~paren:true info) res
        (print_list space (print_lident info)) id_args
        (print_expr info) e

  and print_let_def ?(functor_arg=false) info fmt = function
    | Lvar (pv, e) ->
        fprintf fmt "@[<hov 2>let %a :=@ %a@]"
          (print_lident info) (pv_name pv)
          (* print_ity pv.pv_ity *)
          (print_expr info) e
    | Lsym (rs, _res, args, ef) ->
        let is_result = true in (* todo when result is unit *)
        fprintf fmt "@[<hov 2>function %a (@[%a@]) -> result@ {@[%a@]}@]"
          (print_lident info) rs.rs_name
          (print_list comma (print_vs_arg info)) args
          (* (print_ty info) res *)
          (print_expr info ~is_result) ef;
        forget_vars args
    | Lrec rdef ->
        let print_one fst fmt = function
          | { rec_sym = rs1; rec_args = args; rec_exp = e;
              rec_res = res; rec_svar = s } ->
              fprintf fmt "@[<hov 2>%s %a %a@]"
                (if fst then "let rec" else "and")
                (print_lident info) rs1.rs_name
                (print_fun_type_args info) (args, s, res, e);
              forget_vars args in
        print_list_next newline print_one fmt rdef;
    | Lany (rs, res, []) when functor_arg ->
        fprintf fmt "@[<hov 2>val %a : %a@]"
          (print_lident info) rs.rs_name
          (print_ty info) res;
    | Lany (rs, res, args) when functor_arg ->
        let print_ty_arg info fmt (_, ty, _) =
          fprintf fmt "@[%a@]" (print_ty info) ty in
        fprintf fmt "@[<hov 2>val %a : @[%a@] ->@ %a@]"
          (print_lident info) rs.rs_name
          (print_list arrow (print_ty_arg info)) args
          (print_ty info) res;
        forget_vars args
    | Lany ({rs_name}, _, _) -> check_val_in_drv info rs_name.id_loc rs_name

  and print_expr ?(paren=false) ?(is_result=false) info  fmt e =
    if is_result then begin
      match e.e_node with
      | Econst _
      | Evar _
      | Eapp _ -> fprintf fmt "result := "
      | _ -> ()
    end;
    match e.e_node with
    | Econst _ ->
        let id = match e.e_ity with
          | I { ity_node = Ityapp ({its_ts = ts},_,_) } -> ts.ts_name
          | _ -> assert false in
        (match query_syntax info.info_literal id  with
         | Some s -> syntax_arguments s print_constant fmt [e]
         | None -> failwith "Constants must be of type Int32, Int64, ...")
         (* todo for any right range *)
         (* | _, I { Ity.ity_node = Ity.Ityapp ({Ity.its_ts = { Ty.ts_def = Range range}},[],[])} -> *)
         (* fprintf fmt (protect_on paren "Z.of_string \"%s\"") n) *)
    | Evar pvs ->
        (print_lident info) fmt (pv_name pvs)
    | Elet (let_def, e) ->
        fprintf fmt (protect_on paren "@[%a@]@ @[%a@]")
          (print_let_def info) let_def
          (print_expr info ~is_result) e;
        forget_let_defn let_def
    | Eabsurd ->
        fprintf fmt (protect_on paren "assert false (* absurd *)")
    | Eapp (rs, []) when rs_equal rs rs_true ->
        fprintf fmt "true:bool"
    | Eapp (rs, []) when rs_equal rs rs_false ->
        fprintf fmt "false:bool"
    | Eapp (rs, [])  -> (* avoids parenthesis around values *)
        fprintf fmt "%a" (print_apply info rs) []
    | Eapp (rs, pvl) ->
       fprintf fmt (protect_on paren "%a")
               (print_apply info rs) pvl
    | Ematch (e1, [p, e2], []) ->
        fprintf fmt (protect_on paren "let %a =@ %a in@ %a")
          (print_pat info) p (print_expr info) e1 (print_expr info) e2
    | Ematch (e, pl, []) ->
        fprintf fmt
          (protect_on paren "begin match @[%a@] with@\n@[<hov>%a@]@\nend")
          (print_expr info) e (print_list newline (print_branch info)) pl
    | Eassign al ->
        let assign fmt (rho, rs, e) =
          fprintf fmt "@[<hov 2>%a.%a <-@ %a@]"
            (print_lident info) (pv_name rho) (print_lident info) rs.rs_name
            (print_expr info) e in
        begin match al with
          | [] -> assert false | [a] -> assign fmt a
          | al -> fprintf fmt "@[begin %a end@]" (print_list semi assign) al end
    | Eif (e1, e2, {e_node = Eblock []}) ->
        fprintf fmt
          (protect_on paren
             "@[<hv>@[<hov 2>if@ %a@]@ then begin@;<1 2>@[%a@] end@]")
          (print_expr info) e1 (print_expr info) e2
    | Eif (e1, e2, e3) when is_false e2 && is_true e3 ->
        fprintf fmt (protect_on paren "not %a") (print_expr info ~paren:true) e1
    | Eif (e1, e2, e3) when is_true e2 ->
        fprintf fmt (protect_on paren "@[<hv>%a || %a@]")
          (print_expr info ~paren:true) e1 (print_expr info ~paren:true) e3
    | Eif (e1, e2, e3) when is_false e3 ->
        fprintf fmt (protect_on paren "@[<hv>%a && %a@]")
          (print_expr info ~paren:true) e1 (print_expr info ~paren:true) e2
    | Eif (e1, e2, e3) ->
        fprintf fmt (protect_on paren
                       "@[<hv>@[<hov 2>if@ %a@ then@ begin@ @[%a@] end@]\
                        @;<1 0>else@ begin@;<1 2>@[%a@] end@]")
          (print_expr info) e1 (print_expr info) e2 (print_expr info) e3
    | Eblock [] ->
        fprintf fmt "0:uint8"
    | Eblock [e] ->
        print_expr info fmt e
    | Eblock el ->
        let el,last = Lists.chop_last el in
        fprintf fmt "@[<hv>{@;<1 2>@[%a@]@ %a}@]"
          (print_list space (print_expr info)) el
          (print_expr info ~is_result) last
    | Efun (varl, e) ->
        fprintf fmt (protect_on paren "@[<hov 2>fun %a ->@ %a@]")
          (print_list space (print_vs_arg info)) varl (print_expr info) e
    | Ewhile (e1, e2) ->
        fprintf fmt "@[<hov 2>while %a do@\n%a@ done@]"
          (print_expr info) e1 (print_expr info) e2
    | Eraise (xs, e_opt) ->
        print_raise ~paren info xs fmt e_opt
    | Efor (pv1, pv2, dir, pv3, e) ->
        if is_mapped_to_int info pv1.pv_ity then begin
          fprintf fmt "@[<hov 2>for %a = %a %a %a do@ @[%a@]@ done@]"
            (print_lident info) (pv_name pv1) (print_lident info) (pv_name pv2)
            print_for_direction dir (print_lident info) (pv_name pv3)
            (print_expr info) e;
          forget_pv pv1 end
        else
          let for_id  = id_register (id_fresh "for_loop_to") in
          let cmp, op = match dir with
            | To     -> "Z.leq", "Z.succ"
            | DownTo -> "Z.geq", "Z.pred" in
          fprintf fmt (protect_on paren
                         "@[<hov 2>let rec %a %a =@ if %s %a %a then \
                          begin@ %a; %a (%s %a) end@ in@ %a %a@]")
          (* let rec *) (print_lident info) for_id (print_pv info) pv1
          (* if      *)  cmp (print_pv info) pv1 (print_pv info) pv3
          (* then    *) (print_expr info) e (print_lident info) for_id
                        op (print_pv info) pv1
          (* in      *) (print_lident info) for_id (print_pv info) pv2
    | Ematch (e, [], xl) ->
        fprintf fmt "@[<hv>@[<hov 2>begin@ try@ %a@] with@]@\n@[<hov>%a@]@\nend"
          (print_expr info) e (print_list newline (print_xbranch info false)) xl
    | Ematch (e, bl, xl) ->
        fprintf fmt
          (protect_on paren "begin match @[%a@] with@\n@[<hov>%a@\n%a@]@\nend")
          (print_expr info) e (print_list newline (print_branch info)) bl
          (print_list newline (print_xbranch info true)) xl
    | Eexn (xs, None, e) ->
        fprintf fmt "@[<hv>let exception %a in@\n%a@]"
          (print_uident info) xs.xs_name (print_expr info) e
    | Eexn (xs, Some t, e) ->
        fprintf fmt "@[<hv>let exception %a of %a in@\n%a@]"
          (print_uident info) xs.xs_name (print_ty ~paren:true info) t
          (print_expr info) e
    | Eignore e -> fprintf fmt "ignore (%a)" (print_expr info) e

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hov 2>| %a ->@ @[%a@]@]"
      (print_pat info) p (print_expr info) e;
    forget_pat p

  and print_raise ~paren info xs fmt e_opt =
    match query_syntax info.info_syn xs.xs_name, e_opt with
    | Some s, None ->
        fprintf fmt "raise (%s)" s
    | Some s, Some e ->
        fprintf fmt (protect_on paren "raise (%a)")
          (syntax_arguments s (print_expr info)) [e]
    | None, None ->
        fprintf fmt (protect_on paren "raise %a")
          (print_uident info) xs.xs_name
    | None, Some e ->
        fprintf fmt (protect_on paren "raise (%a %a)")
          (print_uident info) xs.xs_name (print_expr ~paren:true info) e

  and print_xbranch info case fmt (xs, pvl, e) =
    let print_exn fmt () =
      if case then fprintf fmt "exception " else fprintf fmt "" in
    let print_var fmt pv = print_lident info fmt (pv_name pv) in
    match query_syntax info.info_syn xs.xs_name, pvl with
    | Some s, _ -> fprintf fmt "@[<hov 4>| %a%a ->@ %a@]"
        print_exn () (syntax_arguments s print_var) pvl
        (print_expr info ~paren:true) e
    | None, [] -> fprintf fmt "@[<hov 4>| %a%a ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name (print_expr info) e
    | None, [pv] -> fprintf fmt "@[<hov 4>| %a%a %a ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name print_var pv
        (print_expr info) e
    | None, pvl -> fprintf fmt "@[<hov 4>| %a%a (%a) ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name
        (print_list comma print_var) pvl (print_expr info) e

  let print_type_decl info fst fmt its =
    let print_constr fmt (id, cs_args) =
      match cs_args with
      | [] -> fprintf fmt "@[<hov 4>| %a@]" (print_uident info) id
      | l -> fprintf fmt "@[<hov 4>| %a of %a@]" (print_uident info) id
               (print_list star (print_ty ~paren:false info)) l in
    let print_field fmt (is_mutable, id, ty) =
      fprintf fmt "%s%a: @[%a@];" (if is_mutable then "mutable " else "")
        (print_lident info) id (print_ty ~paren:false info) ty in
    let print_def fmt = function
      | None ->
          ()
      | Some (Ddata csl) ->
          fprintf fmt " =@\n%a" (print_list newline print_constr) csl
      | Some (Drecord fl) ->
          fprintf fmt " = %s{@\n%a@\n}"
            (if its.its_private then "private " else "")
            (print_list newline print_field) fl
      | Some (Dalias ty) ->
          fprintf fmt " =@ %a" (print_ty ~paren:false info) ty
      | Some (Drange _) ->
          fprintf fmt " =@ Z.t"
      | Some (Dfloat _) ->
          assert false (*TODO*)
    in
    let attrs = its.its_name.id_attrs in
    if not (is_yul_remove ~attrs) then
      fprintf fmt "@[<hov 2>@[%s %a%a@]%a@]"
        (if fst then "type" else "and") print_tv_args its.its_args
        (print_lident info) its.its_name print_def its.its_def

  let rec is_signature_decl info = function
    | Dtype _ -> true
    | Dlet (Lany _) -> true
    | Dval _ -> true
    | Dlet _ -> false
    | Dexn _ -> true
    | Dmodule (_, dl) -> is_signature info dl

  and is_signature info dl =
    List.for_all (is_signature_decl info) dl

  let extract_functor_args info dl =
    let rec extract args = function
      (* FIXME remove empty args? *)
      (* | Dmodule (_, []) :: dl -> extract args dl *)
      | Dmodule (x, dlx) :: dl when is_signature info dlx ->
          extract ((x, dlx) :: args) dl
      | dl -> List.rev args, dl in
    extract [] dl

  let print_top_val ?(functor_arg=false) info fmt ({pv_vs}, ty) =
    if functor_arg then
      fprintf fmt "@[<hov 2>val %a : %a@]"
        (print_lident info) pv_vs.vs_name (print_ty info) ty
    else
      check_val_in_drv info pv_vs.vs_name.id_loc pv_vs.vs_name

  let rec print_decl ?(functor_arg=false) info fmt = function
    | Dlet ldef ->
        print_let_def info ~functor_arg fmt ldef
    | Dval (pv, ty) ->
        print_top_val info ~functor_arg fmt (pv, ty)
    | Dtype dl ->
        print_list_next newline (print_type_decl info) fmt dl
    | Dexn (xs, None) ->
        fprintf fmt "exception %a" (print_uident info) xs.xs_name
    | Dexn (xs, Some t)->
        fprintf fmt "@[<hov 2>exception %a of %a@]"
          (print_uident info) xs.xs_name (print_ty ~paren:true info) t
    | Dmodule (s, dl) ->
        let args, dl = extract_functor_args info dl in
        let info = { info with info_current_ph = s :: info.info_current_ph } in
        fprintf fmt "@[@[<hov 2>module %s%a@ =@]@\n@[<hov 2>struct@ %a@]@ end" s
          (print_functor_args info) args
          (print_list newline2 (print_decl info)) dl

  and print_functor_args info fmt args =
    let print_sig info fmt dl =
      fprintf fmt "sig@ %a@ end"
        (print_list newline (print_decl info ~functor_arg:true)) dl in
    let print_pair fmt (s, dl) =
      let info = { info with info_current_ph = s :: info.info_current_ph } in
      fprintf fmt "(%s:@ %a)" s (print_sig info) dl in
    fprintf fmt "%a" (print_list space print_pair) args

  let print_decl info fmt decl =
    (* avoids printing the same decl for mutually recursive decls *)
    let memo = Hashtbl.create 64 in
    let decl_name = get_decl_name decl in
    let decide_print id =
      if query_syntax info.info_syn id = None &&
         not (Hashtbl.mem memo decl) then begin
        Hashtbl.add memo decl (); print_decl info fmt decl;
        fprintf fmt "@\n@." end in
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
  Format.fprintf fmt "{%a}"
  (Pp.print_list Pp.nothing (print_decl pargs)) l


let ng suffix ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  (module_name ?fname path mod_name) ^ suffix

let file_gen = ng ".yul"

open Pdriver

let yul_printer =
  { desc_only_flat      = "printer for YUL code";
    file_gen_only_flat  = file_gen;
    decls_printer_only_flat = print_decls;
  }

let () = Pdriver.register_printer_only_flat "yul" yul_printer


(**

let i = (Cryptokit.hash_string (Cryptokit.Hash.keccak 256) "g(uint256)");;
let f j = Int32.shift_left (Int32.of_int (Char.code i.[j])) j;;

*)
