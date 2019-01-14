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

open Format

(** General functions for representations of numeric values *)

exception InvalidConstantLiteral of int * string

type int_value = BigInt.t

type int_literal_kind =
  ILitDec | ILitHex | ILitOct | ILitBin

type int_literal = private {
  il_kind : int_literal_kind;
  il_neg  : bool;
  il_int  : string;
}

type int_constant =
  | IConstVal of int_value
  | IConstLit of int_literal

type real_value = private {
  rv_sig  : BigInt.t;
  rv_pow2 : BigInt.t;
  rv_pow5 : BigInt.t;
}

type real_literal_kind =
  RLitDec | RLitHex

type real_literal = private {
  rl_kind : real_literal_kind;
  rl_neg  : bool;
  rl_int  : string;
  rl_frac : string;
  rl_exp  : string option;
}

type real_constant =
  | RConstVal of real_value
  | RConstLit of real_literal

type constant =
  | ConstInt  of int_constant
  | ConstReal of real_constant

val neg : constant -> constant
val abs : constant -> constant

val compare_real : real_value -> real_value -> int
(** structural comparison; two ordered values might compare differently *)

val compare_const : constant -> constant -> int
(** structural comparison; two mathematically equal values might differ *)

val int_literal : int_literal_kind -> neg:bool -> string -> int_literal
val int_const : BigInt.t -> constant
val int_const_of_int : int -> constant

val real_literal : real_literal_kind -> neg:bool -> int:string -> frac:string -> exp:string option -> real_literal
val real_value : ?pow2:BigInt.t -> ?pow5:BigInt.t -> BigInt.t -> real_value

(** Pretty-printing *)

val print_constant : formatter -> constant -> unit

(** Pretty-printing with conversion *)

type integer_format =
  (string -> unit, Format.formatter, unit) format

type real_format =
  (string -> string -> string -> unit, Format.formatter, unit) format

type part_real_format =
  (string -> string -> unit, Format.formatter, unit) format

type dec_real_format =
  | PrintDecReal of part_real_format * real_format

type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Number_unsupported
  | Number_default
  | Number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type 'a negative_format =
  ((Format.formatter->'a->unit)->'a->unit, Format.formatter,unit) format

type number_support = {
  long_int_support  : bool;
  extra_leading_zeros_support : bool;
  negative_int_support : (string negative_format) number_support_kind;
  dec_int_support   : integer_support_kind;
  hex_int_support   : integer_support_kind;
  oct_int_support   : integer_support_kind;
  bin_int_support   : integer_support_kind;
  def_int_support   : integer_support_kind;
  negative_real_support : ((string * string * string option) negative_format) number_support_kind;
  dec_real_support  : dec_real_format number_support_kind;
  hex_real_support  : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support  : integer_support_kind;
}

val print : number_support -> formatter -> constant -> unit

val print_in_base : int -> int option -> formatter -> BigInt.t -> unit
(** [print_in_base radix digits fmt i] prints the value of [i] in base
    [radix]. If digits is not [None] adds leading 0s to have [digits]
    characters.
    REQUIRES [i] non-negative *)

(** Range checking *)

val to_small_integer : int_literal -> int
(* may raise invalid_argument *)

val compute_int_literal : int_literal -> int_value
val compute_int_constant : int_constant -> int_value
val compute_real_literal : real_literal -> real_value
val compute_real_constant : real_constant -> real_value

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}

val create_range : BigInt.t -> BigInt.t -> int_range

exception OutOfRange of int_constant

val check_range : int_constant -> int_range -> unit
(** [check_range c ir] checks that [c] is in the range described
    by [ir], and raises [OutOfRange c] if not. *)


(** Float checking *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_constant

val compute_float : real_constant -> float_format -> BigInt.t * BigInt.t
(** [compute_float c fp] checks that [c] is a float literal
    representable in the format [fp]. Returns a pair [e,s] with
    [s] the significand (without the hidden bit), and [e] the biased
    exponent. Raises [NonRepresentableFloat c] exception otherwise. *)

val check_float : real_constant -> float_format -> unit
(** [check_float c fp] is the same as [compute_float c fp]
    but does not return any value. *)
