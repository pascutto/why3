open Why3

open Ident
open Term (* only for binop *)
open Cert_syntax


(** Utility functions on <cterm> and <ctask> *)

let rec cterm_node_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTquant (q1, t1), CTquant (q2, t2) when q1 = q2 -> cterm_equal t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> cterm_equal t1 t2
  | _ -> false

and cterm_equal t1 t2 =
  t1.ct_ty = t2.ct_ty && cterm_node_equal t1.ct_node t2.ct_node


let cterm_pos_equal (t1, p1) (t2, p2) =
  cterm_equal t1 t2 && p1 = p2

let ctask_equal cta1 cta2 = Mid.equal cterm_pos_equal cta1 cta2

(* bound variable substitution *)
let rec ct_bv_subst k u t =
  { ct_node = ct_node_bv_subst k u t.ct_node;
    ct_ty   = t.ct_ty }

and ct_node_bv_subst k (u : cterm_node) (t : cterm_node) =
  match t with
  | CTbvar i -> if i = k then u else t
  | CTfvar _ -> t
  | CTapp (t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_bv_subst (k+1) u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_bv_subst k u t)
  | CTtrue -> CTtrue
  | CTfalse -> CTfalse

let ct_open t u = ct_bv_subst 0 u t

(* checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let rec term t = match t.ct_node with
    | CTbvar _ -> false
    | CTapp (t1, t2)
    | CTbinop (_, t1, t2) -> term t1 && term t2
    | CTquant (_, t) -> term (ct_open t (CTfvar di))
    | CTnot t -> term t
    | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* free variable substitution *)
let rec ct_fv_subst z u t =
  { ct_node = ct_node_fv_subst z u t.ct_node;
    ct_ty   = t.ct_ty }

and ct_node_fv_subst z u t = match t with
  | CTfvar x -> if id_equal z x then u else t
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_fv_subst z u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_fv_subst z u t)
  | CTbvar _ | CTtrue | CTfalse -> t

(* variable closing *)
let rec ct_fv_close x k t =
  { ct_node = ct_node_fv_close x k t.ct_node;
    ct_ty   = t.ct_ty }

and ct_node_fv_close x k t = match t with
  | CTbvar _ | CTtrue | CTfalse-> t
  | CTfvar y -> if id_equal x y then CTbvar k else t
  | CTnot t -> CTnot (ct_fv_close x k t)
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) -> CTquant (q, ct_fv_close x (k+1) t)

let ct_close x t = ct_fv_close x 0 t

(* free variable with respect to a term *)
let rec mem_cont x t cont = match t.ct_node with
  | CTfvar y -> cont (id_equal x y)
  | CTapp (t1, t2)
  | CTbinop (_, t1, t2) ->
      mem_cont x t1 (fun m1 ->
      mem_cont x t2 (fun m2 ->
      cont (m1 || m2)))
  | CTquant (_, t)
  | CTnot t -> mem_cont x t cont
  | CTbvar _ | CTtrue | CTfalse -> cont false

let mem x t = mem_cont x t (fun x -> x)

(* checks if the transformation closes the task *)
let rec noskip (r, _) =
  match r with
  | Skip -> false
  | Axiom _ | Trivial -> true
  | Cut (_, c1, c2)
  | Split (c1, c2) -> noskip c1 && noskip c2
  | Unfold c
  | Swap_neg c
  | Destruct (_, _, c)
  | Dir (_, c)
  | Weakening c
  | Intro_quant (_, c)
  | Inst_quant (_, _, c)
  | Revert (_, c) -> noskip c
  | Rewrite (_, _, _, lc) -> List.for_all noskip lc

(* separates hypotheses and goals *)
let split_cta cta =
  let open Mid in
  fold (fun h (ct, pos) (mh, mg) ->
      if pos then mh, add h (ct, pos) mg
      else add h (ct, pos) mh, mg)
    cta (empty, empty)

(* creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let mh, mg = split_cta cta in
  let hg, _ = Mid.choose mg in
  fun ct -> Mid.add hg (ct, true) mh


(** Utility verification functions *)


let find_ident h cta =
  match Mid.find_opt h cta with
  | Some x -> x
  | None -> verif_failed "Can't find ident in the task"

let rec check_rewrite_term tl tr t path =
  (* returns <t> where the instance at <path> of <tl> is replaced by <tr> *)
  match path, t.ct_node with
  | [], _ when cterm_equal t tl -> tr
  | Left::prest, CTbinop (op, t1, t2) ->
      let t1' = check_rewrite_term tl tr t1 prest in
      { ct_node = CTbinop (op, t1', t2);
        ct_ty = t.ct_ty }
  | Right::prest, CTbinop (op, t1, t2) ->
      let t2' = check_rewrite_term tl tr t2 prest in
      { ct_node = CTbinop (op, t1, t2');
        ct_ty = t.ct_ty }
  | _ -> verif_failed "Can't follow the rewrite path"

let check_rewrite cta rev h g terms path : ctask list =
  let rec introduce acc inst_terms t = match t.ct_node, inst_terms with
    | CTbinop (Timplies, t1, t2), _ -> introduce (t1::acc) inst_terms t2
    | CTquant (Tforall, t), inst::inst_terms -> introduce acc inst_terms (ct_open t inst)
    | t, [] -> acc, t
    | _ -> verif_failed "Can't instantiate the hypothesis" in
  let lp, tl, tr =
    let ct, pos = find_ident h cta in
    if pos then verif_failed "Can't use goal as an hypothesis to rewrite" else
      match introduce [] terms ct with
      | lp, CTbinop (Tiff, t1, t2) -> if rev then lp, t1, t2 else lp, t2, t1
      | _ -> verif_failed "Can't find the hypothesis used to rewrite" in
  let rewrite_decl h (te, pos) =
    if id_equal h g
    then check_rewrite_term tl tr te path, pos
    else te, pos in
  Mid.mapi rewrite_decl cta :: List.map (set_goal cta) lp
  (* To check a rewriting rule, you need to :
       • check the rewritten task
       • check every premises of rewritten equality in the current context
   *)


(** This is the main verification function : <check_certif> replays the certificate on a ctask *)

let rec check_certif cta (r, g : certif) : ctask list =
  match r with
    | Skip -> [cta]
    | Axiom h ->
        let th, posh = find_ident h cta in
        let tg, posg = find_ident g cta in
        if not posh && posg
        then if cterm_equal th tg
             then []
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | Trivial ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, pos with
        | CTfalse, false | CTtrue, true -> []
        | _ -> verif_failed "Non trivial hypothesis"
        end
    | Cut (a, c1, c2) ->
        let cta1 = Mid.add g (a, true) cta in
        let cta2 = Mid.add g (a, false) cta in
        check_certif cta1 c1 @ check_certif cta2 c2
    | Split (c1, c2) ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
            let cta1 = Mid.add g (t1, pos) cta in
            let cta2 = Mid.add g (t2, pos) cta in
            check_certif cta1 c1 @ check_certif cta2 c2
        | _ -> verif_failed "Not splittable" end
    | Unfold c ->
        let t, pos = find_ident g cta in
        begin match t.ct_node with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = ctbinop Timplies t1 t2 in
            let imp_neg = ctbinop Timplies t2 t1 in
            let unfolded_iff = ctbinop Tand imp_pos imp_neg, pos in
            let cta = Mid.add g unfolded_iff cta in
            check_certif cta c
        | CTbinop (Timplies, t1, t2) ->
            let nt1 = ctnot t1 in
            let unfolded_imp = ctbinop Tor nt1 t2, pos in
            let cta = Mid.add g unfolded_imp cta in
            check_certif cta c
        | _ -> verif_failed "Nothing to unfold" end
    | Swap_neg c ->
        let t, pos = find_ident g cta in
        let neg_t = match t.ct_node with
          | CTnot t' -> t'
          | _ -> ctnot t in
        let cta = Mid.add g (neg_t, not pos) cta in
        check_certif cta c
    | Destruct (h1, h2, c) ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
            let cta = Mid.remove g cta
                      |> Mid.add h1 (t1, pos)
                      |> Mid.add h2 (t2, pos) in
            check_certif cta c
        | _ -> verif_failed "Nothing to destruct"  end
    | Dir (d, c) ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, d, pos with
        | CTbinop (Tor, t, _), Left, true | CTbinop (Tor, _, t), Right, true
        | CTbinop (Tand, t, _), Left, false | CTbinop (Tand, _, t), Right, false ->
          let cta = Mid.add g (t, pos) cta in
          check_certif cta c
        | _ -> verif_failed "Can't follow a direction" end
    | Weakening c ->
        let cta = Mid.remove g cta in
        check_certif cta c
    | Intro_quant (h, c) ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, pos with
        | CTquant (Tforall, t), true | CTquant (Texists, t), false ->
            if mem h t then verif_failed "non-free variable" else
            let cta = Mid.add g (ct_open t (CTfvar h), pos) cta in
            check_certif cta c
        | _ -> verif_failed "Nothing to introduce" end
    | Inst_quant (h, t_inst, c) ->
        let t, pos = find_ident g cta in
        begin match t.ct_node, pos with
        | CTquant (Tforall, t), false | CTquant (Texists, t), true ->
            let cta = Mid.add h (ct_open t t_inst.ct_node, pos) cta in
            check_certif cta c
        | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
        end
    | Revert (h, c) ->
        let t, pos = find_ident g cta in
        let closed_t = if pos then ctquant Tforall (ct_close h t)
                       else ctquant Texists (ct_close h t) in
        let cta = Mid.add g (closed_t, pos) cta in
        check_certif cta c
    | Rewrite (h, path, rev, lc) ->
        let lcta = check_rewrite cta rev h g [] path in
        List.map2 check_certif lcta lc |> List.concat
