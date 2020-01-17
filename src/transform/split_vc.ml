(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl
open Theory

(*
let split_vc =
  Trans.compose_l
    (Trans.compose Introduction.generalize_intro Split_goal.split_goal_right)
    (Trans.singleton Introduction.simplify_intros)
*)

let intro_attrs = Sattr.singleton Inlining.intro_attr
let stop f = Sattr.mem Term.stop_split f.t_attrs
let asym f = Sattr.mem Term.asym_split f.t_attrs

let intro_var (task, subst) vs =
  let id = id_clone ~attrs:intro_attrs vs.vs_name in
  let ls = create_fsymbol id [] vs.vs_ty in
  let subst = Mvs.add vs (fs_app ls [] vs.vs_ty) subst in
  let d = create_param_decl ls in
  Task.add_decl task d, subst

let rec split_vc_intro acc task pr f =
  Format.printf "+@?";
  let default () =
    Format.printf "-@?";
    let d = create_prop_decl Pgoal pr f in
    let t = Task.add_decl task d in
    let tl = Trans.apply Split_goal.split_goal_right t in
    let add acc t = Trans.apply Introduction.introduce_premises t :: acc in
    List.fold_left add acc tl in
  match f.t_node with
  |  _ when stop f -> default ()
  | Tbinop (Timplies, f1, f2) ->
      begin match split_vc_left task f1 with
      | task -> split_vc_intro acc task pr f2
      | exception Exit -> default () end
  | Tbinop (Tand, f1, f2) when asym f1 ->
      split_vc_intro (split_vc_intro acc task pr f1) task pr
        (t_implies f1 f2)
  | Tbinop (Tand, f1, f2) ->
      split_vc_intro (split_vc_intro acc task pr f1) task pr f2
  | Tquant (Tforall, f1) ->
      let vsl, _, f1 = t_open_quant f1 in
      let task, subst =
        List.fold_left intro_var (task, Mvs.empty) vsl in
      (* preserve attributes and location of f  *)
      let f1 = t_attr_copy f (t_subst subst f1) in
      split_vc_intro acc task pr f1
(*
  | Tlet (t,fb) ->
      let vs, f = t_open_bound fb in
      let ls, mal = ls_of_vs mal vs in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros kn pr mal (expl, hyp_name) f
 *)
(*
  | Tif (f1, f2, f3) ->
     assert false (*TODO*)
 *)
  | _ ->
     default ()

and split_vc_left task f =
  match f.t_node with
  | _ when stop f ->
      let idx =
        let name = Ident.get_hyp_name ~attrs:f.t_attrs in
        id_fresh (Opt.get_def "H" name) ~attrs:intro_attrs in
      let pr = create_prsymbol idx in
      let d = create_prop_decl Paxiom pr f in
      Task.add_decl task d
  | Tbinop (Tand, f1, f2) ->
      split_vc_left (split_vc_left task f1) f2
  | _ ->
      raise Exit

let split_vc t =
  let has_meta m =
    try Task.on_meta m (fun () _ -> raise Exit) () t; false
    with Exit -> true in
  if has_meta Introduction.meta_intro_ls || has_meta Introduction.meta_intro_pr then
     Trans.apply
       (Trans.compose_l Split_goal.split_goal_right
          (Trans.singleton Introduction.introduce_premises)) t
  else
    let g, task = Task.task_separate_goal t in
    match g.td_node with
    | Decl { d_node = Dprop (Pgoal, pr, f) } ->
       let tl = split_vc_intro [] task pr f in
       List.rev tl
    | _ -> assert false

let split_vc = Trans.store split_vc

let split_vc =
  Trans.compose_l
    (Trans.compose Introduction.generalize_intro split_vc)
    (Trans.singleton Introduction.subst)

let () = Trans.register_transform_l
           "split_vc" split_vc
           ~desc:"The@ recommended@ splitting@ transformation@ to@ apply@ \
              on@ VCs@ generated@ by@ WP@ (split_goal_right@ followed@ \
              by@ introduce_premises@ followed@ by@ subst_all)."
