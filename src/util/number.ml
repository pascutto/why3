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

let debug_float = Debug.register_info_flag "float"
  ~desc:"Avoid@ catching@ exceptions@ in@ order@ to@ get@ \
         float@ literal@ checks@ messages."

(** Construction *)
type int_value = BigInt.t

type int_literal_kind =
  ILitDec | ILitHex | ILitOct | ILitBin

type int_literal = {
  il_kind : int_literal_kind;
  il_neg  : bool;
  il_int  : string;
}

type int_constant =
  | IConstVal of int_value
  | IConstLit of int_literal

type real_value = {
  rv_sig  : BigInt.t;
  rv_pow2 : BigInt.t;
  rv_pow5 : BigInt.t;
}

type real_literal_kind =
  RLitDec | RLitHex

type real_literal = {
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

let compare_real { rv_sig = s1; rv_pow2 = p21; rv_pow5 = p51 } { rv_sig = s2; rv_pow2 = p22; rv_pow5 = p52 } =
  let c = BigInt.compare s1 s2 in
  if c <> 0 then c else
  let c = BigInt.compare p21 p22 in
  if c <> 0 then c else
  BigInt.compare p51 p52

let compare_const c1 c2 =
  match c1, c2 with
  | ConstInt (IConstVal i1), ConstInt (IConstVal i2) ->
      BigInt.compare i1 i2
  | ConstReal (RConstVal r1), ConstReal (RConstVal r2) ->
      compare_real r1 r2
  | _, _ ->
      Pervasives.compare c1 c2

let neg = function
  | ConstInt (IConstVal i) -> ConstInt (IConstVal (BigInt.minus i))
  | ConstInt (IConstLit i) -> ConstInt (IConstLit { i with il_neg = not i.il_neg })
  | ConstReal (RConstVal r) -> ConstReal (RConstVal { r with rv_sig = BigInt.minus r.rv_sig })
  | ConstReal (RConstLit r) -> ConstReal (RConstLit { r with rl_neg = not r.rl_neg })

let abs = function
  | ConstInt (IConstVal i) -> ConstInt (IConstVal (BigInt.abs i))
  | ConstInt (IConstLit i) -> ConstInt (IConstLit { i with il_neg = false })
  | ConstReal (RConstVal r) -> ConstReal (RConstVal { r with rv_sig = BigInt.abs r.rv_sig })
  | ConstReal (RConstLit r) -> ConstReal (RConstLit { r with rl_neg = false })

exception InvalidConstantLiteral of int * string
let invalid_constant_literal n s = raise (InvalidConstantLiteral(n,s))

let check_integer_literal n f s =
  let l = String.length s in
  if l = 0 then invalid_constant_literal n s;
  for i = 0 to l-1 do
    if not (f s.[i]) then invalid_constant_literal n s;
  done

let is_hex = function '0'..'9' | 'A'..'F' | 'a'..'f' -> true | _ -> false
let is_dec = function '0'..'9' -> true | _ -> false
let is_oct = function '0'..'7' -> true | _ -> false
let is_bin = function '0'..'1' -> true | _ -> false

let int_literal k ~neg s =
  let radix, check =
    match k with
    | ILitBin -> 2, is_bin
    | ILitOct -> 8, is_oct
    | ILitDec -> 10, is_dec
    | ILitHex -> 16, is_hex in
  check_integer_literal radix check s;
  { il_kind = k; il_neg = neg; il_int = s }

let int_const n =
  ConstInt (IConstVal n)

let int_const_of_int n =
  int_const (BigInt.of_int n)

let check_exp e =
  let e = if e.[0] = '-' then String.sub e 1 (String.length e - 1) else e in
  check_integer_literal 10 is_dec e

let real_literal k ~neg ~int ~frac ~exp =
  let radix, check =
    match k with
    | RLitDec -> 10, is_dec
    | RLitHex -> 16, is_hex in
  if int  <> "" then check_integer_literal radix check int;
  if frac <> "" then check_integer_literal radix check frac;
  Opt.iter check_exp exp;
  { rl_kind = k; rl_neg = neg; rl_int = int; rl_frac = frac; rl_exp = exp }

let rec normalize v p e =
  let (d,m) = BigInt.computer_div_mod v p in
  if BigInt.eq m BigInt.zero then
    let e2 = BigInt.add e e in
    let (v,f) = normalize d (BigInt.mul p p) e2 in
    let (d,m) = BigInt.computer_div_mod v p in
    if BigInt.eq m BigInt.zero then (d, BigInt.add f e2) else (v, BigInt.add f e)
  else (v, BigInt.zero)

let normalize v p =
  normalize v (BigInt.of_int p) BigInt.one

let real_value ?(pow2 = BigInt.zero) ?(pow5 = BigInt.zero) i =
  if BigInt.eq i BigInt.zero then { rv_sig = i; rv_pow2 = i; rv_pow5 = i }
  else
    let (i, p2) = normalize i 2 in
    let (i, p5) = normalize i 5 in
    { rv_sig = i; rv_pow2 = BigInt.add pow2 p2; rv_pow5 = BigInt.add pow5 p5 }

let compute_any radix s =
  let n = String.length s in
  let rec compute acc i =
    if i = n then
      acc
    else begin
      let v = match s.[i] with
        | '0'..'9' as c -> Char.code c - Char.code '0'
        | 'A'..'Z' as c -> 10 + Char.code c - Char.code 'A'
        | 'a'..'z' as c -> 10 + Char.code c - Char.code 'a'
        | _ -> assert false in
      assert (v < radix);
      compute (BigInt.add_int v (BigInt.mul_int radix acc)) (i + 1)
    end in
  (compute BigInt.zero 0)

(** Printing *)

let compute_int_literal { il_kind = k ; il_neg = n; il_int = i } =
  let i =
    match k with
    | ILitBin -> compute_any 2 i
    | ILitOct -> compute_any 8 i
    | ILitDec -> compute_any 10 i
    | ILitHex -> compute_any 16 i in
  if n then BigInt.minus i else i

let compute_int_constant = function
  | IConstVal n -> n
  | IConstLit l -> compute_int_literal l

let compute_real_literal { rl_kind = k; rl_neg = n; rl_int = i; rl_frac = f; rl_exp = e } =
  let exp_parser e = match e.[0] with
    | '-' -> BigInt.minus (compute_any 10 (String.sub e 1 (String.length e - 1)))
    | _   -> compute_any 10 e
  in
  let radix = match k with RLitDec -> 10 | RLitHex -> 16 in
  let s = compute_any radix (i ^ f) in
  let s = if n then BigInt.minus s else s in
  let e = match e with Some e -> exp_parser e | None -> BigInt.zero in
  let e = BigInt.add_int (- String.length f) e in
  match k with
  | RLitDec -> real_value ~pow2:e ~pow5:e s
  | RLitHex -> real_value ~pow2:e ~pow5:BigInt.zero s

let compute_real_constant = function
  | RConstVal v -> v
  | RConstLit l -> compute_real_literal l

let to_small_integer i =
  BigInt.to_int (compute_int_literal i)

let any_to_dec radix s =
  BigInt.to_string (compute_any radix s)

let power2 n =
  BigInt.to_string (BigInt.pow_int_pos 2 n)

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
  ((Format.formatter->'a->unit)->'a->unit,Format.formatter,unit) format

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

let check_support support default do_it try_next v =
  match support with
  | Number_unsupported -> try_next v
  | Number_default -> do_it (Opt.get default) v
  | Number_custom f -> do_it f v

let force_support support do_it v =
  match support with
  | Number_unsupported -> assert false
  | Number_default -> assert false
  | Number_custom f -> do_it f v

let simplify_max_int = BigInt.of_string "2147483646"

let remove_minus e =
  if e.[0] = '-' then begin
    let e = Bytes.of_string e in
    Bytes.set e 0 'm';
    Bytes.unsafe_to_string e
  end else e

let print_dec_int support fmt i =
  let fallback i =
    force_support support.def_int_support (fprintf fmt) i in
  if not support.long_int_support &&
     (BigInt.compare (BigInt.of_string i) simplify_max_int > 0) then
    fallback i
  else
    check_support support.dec_int_support (Some "%s") (fprintf fmt)
    fallback i

let print_hex_int support fmt =
  check_support support.hex_int_support (Some "0x%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 16 i))

let print_oct_int support fmt =
  check_support support.oct_int_support (Some "0o%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 8 i))

let print_bin_int support fmt =
  check_support support.bin_int_support (Some "0b%s")
    (fun s i -> assert support.long_int_support; fprintf fmt s i)
  (fun i -> print_dec_int support fmt (any_to_dec 2 i))

let remove_leading_zeros support s =
  if support.extra_leading_zeros_support then s else
  let len = String.length s in
  let rec aux i =
    if i+1 < len && s.[i] = '0' then aux (i+1) else i
  in
  let i = aux 0 in
  String.sub s i (len - i)

let print_dec_real support fmt =
  check_support support.dec_real_support
    (Some (PrintDecReal ("%s.%s", "%s.%se%s")))
    (fun (PrintDecReal (noexp,full)) i f e ->
      match e with
      | None -> fprintf fmt noexp
          (remove_leading_zeros support i)
          (if f = "" then "0" else f)
      | Some e -> fprintf fmt full
          (remove_leading_zeros support i)
          (if f = "" then "0" else f)
          (remove_leading_zeros support e))
    (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let e = Opt.fold (fun _ -> int_of_string) 0 e in
      let e = e - String.length f in
      if e = 0 then
        fprintf fmt exp_zero (remove_leading_zeros support (i ^ f))
      else if e > 0 then
        fprintf fmt exp_pos (remove_leading_zeros support (i ^ f))
          ("1" ^ String.make e '0')
      else
        fprintf fmt exp_neg (remove_leading_zeros support (i ^ f))
          ("1" ^ String.make (-e) '0'))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "%s_%s_e%s" i f
      (match e with None -> "0" | Some e -> remove_minus e)))
  ))

let print_hex_real support fmt =
  check_support support.hex_real_support
    (Some "0x%s.%sp%s")
    (fun s i f e -> fprintf fmt s i
      (if f = "" then "0" else f)
      (Opt.get_def "0" e))
  (* TODO: add support for decay to decimal floats *)
  (check_support support.frac_real_support None
    (fun (PrintFracReal (exp_zero, exp_pos, exp_neg)) i f e ->
      let f = if f = "0" then "" else f in
      let dec = any_to_dec 16 (i ^ f) in
      let e = Opt.fold (fun _ -> int_of_string) 0 e in
      let e = e - 4 * String.length f in
      if e = 0 then
        fprintf fmt exp_zero dec
      else if e > 0 then
        fprintf fmt exp_pos dec (power2 e)
      else
        fprintf fmt exp_neg dec (power2 (-e)))
  (force_support support.def_real_support
    (fun def i f e -> fprintf fmt def (sprintf "0x%s_%s_p%s" i f
      (match e with None -> "0" | Some e -> remove_minus e)))
  ))

let print_int_literal support fmt k n i =
  let p = match k with
    | ILitBin -> print_bin_int
    | ILitOct -> print_oct_int
    | ILitDec -> print_dec_int
    | ILitHex -> print_hex_int in
  if n then
    check_support support.negative_int_support (Some "(- %a)")
      (fun def n -> fprintf fmt def (p support) n)
      (fun _ -> assert false)
      i
  else
    p support fmt i

let print_int_constant support fmt = function
  | IConstVal i ->
      let (n,i) = if BigInt.lt i BigInt.zero then true, BigInt.abs i else false, i in
      print_int_literal support fmt ILitDec n (BigInt.to_string i)
  | IConstLit { il_kind = k; il_neg = n; il_int = i } ->
      print_int_literal support fmt k n i

let print_real_literal support fmt k n i f e =
  let p = match k with
    | RLitDec -> print_dec_real
    | RLitHex -> print_hex_real in
  let p support fmt (i, f, e) = p support fmt i f e in
  if n then
    check_support support.negative_real_support (Some "(- %a)")
      (fun def n -> fprintf fmt def (p support) n)
      (fun _ -> assert false)
      (i, f, e)
  else
    p support fmt (i, f, e)

let print_real_constant support fmt = function
  | RConstVal { rv_sig = i; rv_pow2 = p2; rv_pow5 = p5 } ->
      let (n,i) = if BigInt.lt i BigInt.zero then true, BigInt.abs i else false, i in
      let e = BigInt.min p2 p5 in
      let i = BigInt.mul i (BigInt.pow_int_pos_bigint 2 (BigInt.sub p2 e)) in
      let i = BigInt.mul i (BigInt.pow_int_pos_bigint 5 (BigInt.sub p5 e)) in
      print_real_literal support fmt RLitDec n (BigInt.to_string i) "" (Some (BigInt.to_string e))
  | RConstLit { rl_kind = k; rl_neg = n; rl_int = i; rl_frac = f; rl_exp = e } ->
      print_real_literal support fmt k n i f e

let print support fmt = function
  | ConstInt i -> print_int_constant support fmt i
  | ConstReal r -> print_real_constant support fmt r







let char_of_int i =
  if i < 10 then
    Char.chr (i + Char.code '0')
  else
    Char.chr (i + Char.code 'A' - 10)

open BigInt

let print_zeros fmt n =
  for _i = 0 to n - 1 do
    pp_print_char fmt '0'
  done

let rec print_in_base_aux radix digits fmt i =
  if lt i radix then begin
    begin match digits with
      | Some n -> print_zeros fmt (n - 1)
      | None -> ()
    end;
    fprintf fmt "%c" (char_of_int (to_int i))
  end
  else
    let d,m = euclidean_div_mod i radix in
    let digits = Opt.map ((+) (-1)) digits in
    print_in_base_aux radix digits fmt d;
    fprintf fmt "%c" (char_of_int (to_int m))

let print_in_base radix digits fmt i =
  print_in_base_aux (of_int radix) digits fmt i

(** Range checks *)

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}

let create_range lo hi =
  { ir_lower = lo;
    ir_upper = hi;
}

exception OutOfRange of int_constant

let check_range c {ir_lower = lo; ir_upper = hi} =
  let cval = compute_int_constant c in
  if BigInt.lt cval lo || BigInt.gt cval hi then raise (OutOfRange c)

(** Float checks *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_constant

let float_parser c =
  let { rv_sig = i; rv_pow2 = p2; rv_pow5 = p5 } = compute_real_constant c in
  (* get the value i and e such that c = i * 2 ^ e *)
  if lt p5 zero then raise (NonRepresentableFloat c)
  else
    let i = BigInt.mul i (BigInt.pow_int_pos_bigint 5 p5) in
    i, p2

let compute_float c fp =
  let eb = BigInt.of_int fp.fp_exponent_digits in
  let sb = BigInt.of_int fp.fp_significand_digits in
  (* 2 ^ (sb - 1)    min representable normalized significand*)
  let smin = pow_int_pos_bigint 2 (sub sb one) in
  (* (2 ^ sb) - 1    max representable normalized significand*)
  let smax = sub (pow_int_pos_bigint 2 sb) one in
  (* 2 ^ (eb - 1)    exponent of the infinities *)
  let emax = pow_int_pos_bigint 2 (sub eb one) in
  (* 1 - emax        exponent of the denormalized *)
  let eden = sub one emax in
  (* 3 - emax - sb   smallest denormalized' exponent *)
  let emin = sub (add (of_int 2) eden) sb in

  (* get [s] and [e] such that "c = s * 2 ^ e" *)
  let s, e = float_parser c in
  let s, e = ref s, ref e in

  (* if s = 0 stop now *)
  if eq !s zero then
    zero, zero

  else begin

    (* if s is too big or e is too small, try to remove trailing zeros
       in s and incr e *)
    while gt !s smax || lt !e emin do
      let new_s, rem = euclidean_div_mod !s (of_int 2) in
      if not (eq rem zero) then begin
        Debug.dprintf debug_float "Too many digits in significand.";
        raise (NonRepresentableFloat c);
      end else begin
        s := new_s;
        e := succ !e
      end
    done;

    (* if s is too small and e is too big, add trailing zeros in s and
       decr e *)
    while lt !s smin && gt !e emin do
      s := mul_int 2 !s;
      e := pred !e
    done;

    Debug.dprintf debug_float " = %s * 2 ^ %s@." (to_string !s) (to_string !e);

    if lt !s smin then begin
      (* denormal case *)

      Debug.dprintf debug_float "final: c = 0.[%s] * 2 ^ ([0] - bias + 1); bias=%s, i.e, 0[%a][%a]@."
        (to_string !s) (to_string (sub emax one)) (print_in_base 2 (Some (to_int eb))) zero
      (print_in_base 2 (Some (to_int (sub sb one)))) !s;

      zero, !s

    end else begin
      (* normal case *)

      (* normalize the exponent *)
      let fe = add !e (sub sb one) in

      (* now that s and e are in shape, check that e is not too big *)
      if ge fe emax then begin
        Debug.dprintf debug_float "Exponent too big.";
        raise (NonRepresentableFloat c)
      end;

      (* add the exponent bia to e *)
      let fe = add fe (sub emax one) in
      let fs = sub !s smin in

      Debug.dprintf debug_float "final: c = 1.[%s] * 2 ^ ([%s] - bias); bias=%s, i.e, 0[%a][%a]@."
        (to_string fs) (to_string fe) (to_string (sub emax one))
        (print_in_base 2 (Some (to_int eb))) fe
        (print_in_base 2 (Some (to_int (sub sb one)))) fs;

      assert (le zero fs && lt fs (pow_int_pos_bigint 2 (sub sb one))
              && le zero fe && lt fe (sub (pow_int_pos_bigint 2 eb) one));

      fe, fs
    end
  end

let check_float c fp = ignore (compute_float c fp)


let full_support =
  {
    long_int_support = true;
    extra_leading_zeros_support = true;
    negative_int_support = Number_default;
    dec_int_support = Number_default;
    hex_int_support = Number_default;
    oct_int_support = Number_default;
    bin_int_support = Number_default;
    def_int_support = Number_default;
    negative_real_support = Number_default;
    dec_real_support = Number_default;
    hex_real_support = Number_default;
    frac_real_support = Number_default;
    def_real_support = Number_default;
  }

(*

let print_integer_literal fmt = function
  | IConstDec s -> fprintf fmt "%s" s
  | IConstHex s -> fprintf fmt "0x%s" s
  | IConstOct s -> fprintf fmt "0o%s" s
  | IConstBin s -> fprintf fmt "0b%s" s

let print_real_literal fmt = function
  | RConstDec (i,f,None)   -> fprintf fmt "%s.%s" i f
  | RConstDec (i,f,Some e) -> fprintf fmt "%s.%se%s" i f e
  | RConstHex (i,f,Some e) -> fprintf fmt "0x%s.%sp%s" i f e
  | RConstHex (i,f,None)   -> fprintf fmt "0x%s.%s" i f

let print_unsigned_constant fmt = function
  | ConstInt c  -> print_integer_literal fmt c
  | ConstReal c -> print_real_literal fmt c

let print_constant fmt c =
  if c.is_positive then print_unsigned_constant fmt c.abs_value
  else fprintf fmt "-%a" print_unsigned_constant c.abs_value
 *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | InvalidConstantLiteral (n,s) ->
      fprintf fmt "Invalid integer literal in base %d: '%s'" n s
  | NonRepresentableFloat c ->
      fprintf fmt "Invalid floating point literal: '%a'"
        (print_real_constant full_support) c
  | OutOfRange c ->
      fprintf fmt "Integer literal %a is out of range"
              (print_int_constant full_support) c
  | _ -> raise exn)

let print_constant = print full_support
