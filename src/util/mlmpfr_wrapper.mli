(* TODO This wrapper should eventually be removed !
   For documentation refer to the gmp documentation.
*)

(* Wrapper for gmp's MPFR:
   MPFR installed -> implemented with mlgmp
   MPFR not installed -> dummy implementation
*)

type m
type 'a tt
type t = m tt

(* Exception to be raised if mpfr is not installed *)
exception Not_Implemented

val set_emin: int -> unit
val set_emax: int -> unit
val set_default_prec: int -> unit
val get_default_prec: unit -> int

type round =
  | Near     (* To_Nearest *)
  | Zero     (* Toward_Zero *)
  | Up       (* Toward_Plus_Infinity *)
  | Down     (* Toward_Minus_Infinity *)
  | Away     (* Away_From_Zero *)
  | Faith    (* Faithful *)
  | NearAway

(* Init function *)
val init2: int -> t
(* [init2 precision]: returns an initialized NaN number *)

(* Elementary operations  *)
val add : t (* out *) -> 'a tt -> 'b tt -> round -> int
val neg : t (* out *) -> 'a tt -> round -> int
val mul : t (* out *) -> 'a tt -> 'b tt -> round -> int
val div : t (* out *) -> 'a tt -> 'b tt -> round -> int
val sqrt: t (* out *) -> 'a tt -> round -> int
val sub : t (* out *) -> 'a tt -> 'b tt -> round -> int
val abs : t (* out *) -> 'a tt -> round -> int
val fma : t (* out *) -> 'a tt -> 'b tt -> 'c tt -> round -> int
val rint: t (* out *) -> 'a tt -> round -> int
val exp : t (* out *) -> 'a tt -> round -> int
val log : t (* out *) -> 'a tt -> round -> int

val min : t (* out *) -> 'a tt -> 'b tt -> round -> int
val max : t (* out *) -> 'a tt -> 'b tt -> round -> int

val sgn: 'a tt -> int

val subnormalize : 'a tt -> round -> int

val make_from_str: prec:int -> base:int -> rnd:round -> string -> m tt

val convert_string: base:int -> t -> string

(* Comparison functions *)

val greater_p : 'a tt -> 'b tt -> bool
val greaterequal_p : 'a tt -> 'b tt -> bool
val less_p : 'a tt -> 'b tt -> bool
val lessequal_p : 'a tt -> 'b tt -> bool
val equal_p : 'a tt -> 'b tt -> bool
val lessgreater_p : 'a tt -> 'b tt -> bool


(* Reallocating version of get_zero and get_one to avoid precision errors *)
val get_zero: int -> t
val get_one: int -> t

val zero_p: 'a tt -> bool
val nan_p : 'a tt -> bool
val inf_p : 'a tt -> bool

(* Constants *)
val const_pi: t -> round -> int
