open Decl
open Term
open Ident


(* We have to keep all the attributes given on all possible occurences of f in
   the term: we cannot let any get erased by a new one. *)
let add_clone f attrs clones =
  if Mls.mem f clones then
    let old_clone = Mls.find f clones in
    let attrs = Sattr.union attrs old_clone.ls_name.id_attrs in
    let new_clone =
      create_lsymbol (Ident.id_clone f.ls_name ~attrs) f.ls_args f.ls_value
    in
    Mls.add f new_clone clones
  else
    let new_clone =
      create_lsymbol (Ident.id_clone f.ls_name ~attrs) f.ls_args f.ls_value
    in
    Mls.add f new_clone clones

let rec collect_new_term acc t =
  t_fold (fun acc t ->
      match t.t_node with
      | Tapp (f, []) when not (Sattr.is_empty t.t_attrs) ->
          collect_new_term (add_clone f t.t_attrs acc) t
      | _ -> collect_new_term acc t) acc t

(* [collect_new_decl: task -> (lsymbol Mls.t)]
   Returns a mapping from lsymbol to new cloned lsymbol which contains the
   attributes (that are directly associated to it in the term).
   Example term:
   ([@some_attribute] my_var) + 1
   returns:
   (my_var -> my_var_cloned) with
   my_var_cloned = {my_var with attrs = my_var.attrs U some_attribute}
*)
let collect_new_decl : lsymbol Mls.t Trans.trans =
  Trans.fold_decl (fun d acc ->
    match d.d_node with
    | Dprop (_, _pr, t) ->
      collect_new_term acc t
    | _ -> acc) Mls.empty

let replace_ls col ls =
  if Mls.mem ls col then
    Mls.find ls col
  else
    ls

(** [replace] functions which are basically doing [replace_ls] on the
    subelements the function apply to. *)

let rec t_replace_ls col t =
  t_map (fun t -> match t.t_node with
  | Tapp (f, []) when Mls.mem f col ->
      t_app_infer (Mls.find f col) []
  | _ ->
      t_replace_ls col t) t

let replace_cons col (c, lsoptlist) =
  let c = replace_ls col c in
  let lsoptlist =
    List.map (fun lsopt -> Opt.map (replace_ls col) lsopt) lsoptlist
  in
  (c, lsoptlist)

(* This replaces all lsymbols found in the task with corresponding ones from
   [col].
*)
let replace_with_collection (col: lsymbol Mls.t) : Task.task Trans.trans =
  Trans.decl (fun d ->
      match d.d_node with
      | Dparam ls when Mls.mem ls col ->
          let new_ls = Mls.find ls col in
          [Decl.create_param_decl new_ls]
      | Dparam _ls -> [d]
      | Dprop (k, pr, t) ->
          let new_t = t_replace_ls col t in
          [Decl.create_prop_decl k pr new_t]
      | Dlogic als ->
          let replace ls ls_d : logic_decl =
            let (vl, t) = open_ls_defn ls_d in
            let new_ls = replace_ls col ls in
            make_ls_defn new_ls vl (t_replace_ls col t)
          in
          let logic_decls : logic_decl list =
            List.map (fun (ls, ls_def) ->
                replace ls ls_def) als
          in
          [Decl.create_logic_decl logic_decls]
      | Dtype _ty -> [d]
      | Ddata dl ->
          let dl = List.map (fun (ty, cl) ->
              ty, List.map (replace_cons col) cl) dl in
          [create_data_decl dl]
      | Dind (is, idl) ->
          let idl = List.map (fun (ls, prtlist) ->
              let ls = replace_ls col ls in
              let prtlist =
                List.map (fun (pr, t) -> (pr, t_replace_ls col t)) prtlist
              in
              (ls, prtlist)) idl
          in
          [create_ind_decl is idl]
    ) None

let attr_to_ls = Trans.bind collect_new_decl replace_with_collection
