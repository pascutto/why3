(* Dummy implementation for mpfr that always raise Not_implemented *)

exception Not_Implemented

type m = unit
type 'a tt = 'a
type t = m tt

type round =
  | Near     (* To_Nearest *)
  | Zero     (* Toward_Zero *)
  | Up       (* Toward_Plus_Infinity *)
  | Down     (* Toward_Minus_Infinity *)
  | Away     (* Away_From_Zero *)
  | Faith    (* Faithful *)
  | NearAway

let set_emin _ = ()
let set_emax _ = ()
let set_default_prec _ = ()
let get_default_prec _ = 0

(* Elementary operations *)
let add _ _ _ _ = raise Not_Implemented
let neg _ _ _   = raise Not_Implemented
let mul _ _ _ _ = raise Not_Implemented
let div _ _ _ _ = raise Not_Implemented
let sqrt _ _ _  = raise Not_Implemented
let sub _ _ _ _ = raise Not_Implemented
let abs _ _ _ = raise Not_Implemented
let fma _ _ _ _ _ = raise Not_Implemented
let rint _ _ _ = raise Not_Implemented
let exp _ _ _ = raise Not_Implemented
let log _ _ _ = raise Not_Implemented


let min _ _ _ _ = raise Not_Implemented
let max _ _ _ _ = raise Not_Implemented

let sgn _ = raise Not_Implemented

let init2 _ = ()

let subnormalize _ _ = 0 (* Used outside of try *)


let get_zero _ = ()
let get_one _ = ()

let make_from_str ~prec:_ ~base:_ ~rnd:_ _ = ()

let convert_string ~base:_ _ = "Error: MPFR not configured"

(* Comparison functions *)

let greater_p _ _      = raise Not_Implemented
let greaterequal_p _ _ = raise Not_Implemented
let less_p _ _         = raise Not_Implemented
let lessequal_p _ _    = raise Not_Implemented
let equal_p _ _        = raise Not_Implemented
let lessgreater_p _ _  = raise Not_Implemented

let zero_p _ = raise Not_Implemented
let nan_p _ = raise Not_Implemented
let inf_p _ = raise Not_Implemented

(* Constants *)
let const_pi _ _ = 0
