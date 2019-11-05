(* TODO This wrapper should eventually be removed ! *)

(* Exception to be raised if mpfr is not installed *)
exception Not_Implemented

include Mpfr

let subnormalize e rnd =
  (* We will always ignore the ternary value so we set the propagated ternary
     value to 0 *)
  subnormalize e 0 rnd

let make_from_str ~prec ~base ~rnd s =
  let res = init2 prec in
  let () = set_str res s ~base rnd in
  res

let get_zero prec =
  let res = init2 prec in
  let (_: int) = set_si res 0 Near (* exact *) in
  res

let get_one prec =
  let res = init2 prec in
  let (_: int) = set_si res 1 Near (* exact *) in
  res

(* TBI: use the erange flag in comparison functions ? *)
let less_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b < 0

let greater_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b > 0

let lessequal_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b <= 0

let greaterequal_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b >= 0

let equal_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b = 0

let lessgreater_p a b =
  not (nan_p a) && not (nan_p b) && cmp a b <> 0

(* Function used for printing *)
let convert_string ~base f =
  (* Example: deci = 20001, exp = 23 ->
     number represented is: 0.20001 * base ^ 23*)
  (* When NaN or infinites the string begins with @ *)
  let (deci, exp) = get_str ~base ~digits:0 f Near in
  if String.contains deci '@' then
    deci
  else
  if base = 16 then
    "0x0." ^ deci ^ "p" ^ string_of_int exp
  else
  if base = 10 then
    "0." ^ deci ^ "E" ^ string_of_int exp
  else
    (* TODO not implemented. Using @ because the number in the base are
       letters. *)
    "?0." ^ deci ^ "@" ^ string_of_int exp
