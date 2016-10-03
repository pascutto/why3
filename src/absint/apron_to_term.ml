open Apron
open Term

module Apron_to_term(E: sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct

  exception Cannot_be_expressed

  let th_int = Env.read_theory E.env ["int"] "Int"
  let int_tys = Theory.(ns_find_ts th_int.th_export ["int"])
  let ty_int = (Ty.ty_app int_tys [])
  let int_zero = fs_app Theory.(ns_find_ls th_int.th_export ["zero"]) [] ty_int
  let int_le = Theory.(ns_find_ls th_int.th_export ["infix <="])
  let int_lt = Theory.(ns_find_ls th_int.th_export ["infix <"])
  let int_add = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["infix +"]) a ty_int
  let int_minus = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["infix -"]) a ty_int
  let int_mult = fun a -> fs_app Theory.(ns_find_ls th_int.th_export ["infix *"]) a ty_int
  (*let int_minus_u = fun a -> Theory.(ns_find_ls th_int.th_export ["infix -_"]) a ty_int (* does not work for some weird reasons *) *)
  let int_minus_u = (fun a -> int_minus (int_zero::a))

  let coeff_to_term = function
    | Coeff.Scalar(s) ->
      let i = int_of_string (Scalar.to_string s) in
      let s = string_of_int (abs i) in
      let n = Number.int_const_dec s in
      let n = Number.ConstInt n in

      if i > 0 then
        Some (t_const n)
      else if i < 0 then
        Some (int_minus_u [t_const n])
      else
        None
    | Coeff.Interval(_) -> raise Cannot_be_expressed

  let lincons_to_term l variable_mapping =
    let open Ty in
    let term = ref int_zero in
    Lincons1.iter (fun c v ->
        match coeff_to_term c with
        | Some c ->
          let v = variable_mapping v in
          term := int_add [!term; int_mult [c; v]];
        | None -> ()
      ) l;
    let c = coeff_to_term (Lincons1.get_cst l) in
    let term = match c with
      | None -> !term
      | Some c ->
        int_add [c; !term] in
    match Lincons1.get_typ l with
    | Lincons1.EQ -> ps_app ps_equ [term; int_zero]
    | Lincons1.SUP -> ps_app int_lt [int_zero; term]
    | Lincons1.SUPEQ -> ps_app int_le [int_zero; term;]
    | Lincons1.DISEQ ->  t_not (ps_app ps_equ [term; int_zero])

  let lincons_array_to_term l variable_mapping =
    let n = Lincons1.array_length l in
    let t = ref (Term.t_true) in
    for i = 0 to n - 1 do
      t := t_and !t (lincons_to_term (Lincons1.array_get l i) variable_mapping);
    done;
    !t

  let domain_to_term man d variable_mapping =
    let a = Abstract1.to_lincons_array man d in
    lincons_array_to_term a variable_mapping

end
