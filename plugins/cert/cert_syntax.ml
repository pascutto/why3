open Why3

open Term
open Ident
open Decl
open Theory
open Task
open Format


(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cterm = {
  ct_node : cterm_node;
  ct_ty : bool }

and cterm_node =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTapp of cterm * cterm
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of quant * cterm (* forall binding *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

let formula ctn = { ct_node = ctn; ct_ty = true }

let ctbvar i = formula (CTbvar i)

let ctfvar id = formula (CTfvar id)

let ctbinop bop ct1 ct2 = formula (CTbinop (bop, ct1, ct2))

let ctquant q ct = formula (CTquant (q, ct))

let ctnot ct = formula (CTnot ct)

let cttrue = formula CTtrue

let ctfalse = formula CTfalse

type ctask = (cterm * bool) Mid.t
(* We will denote a ctask <M> by <Γ ⊢ Δ> where :
   • <Γ> contains all the declarations <H : P> where <H> is mapped to <(P, false)> in <M>
   • <Δ> contains all the declarations <H : P> where <H> is mapped to <(P, true)> in <M>
*)

type dir = Left | Right
type path = dir list

type certif = rule * ident
(* The ident indicates where to apply the rule.
   In the following rules, we will call it <G> *)

(* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>,
   it is defined as the function <Cert_verif.check_certif> *)
and rule =
  | Skip
  (* Skip ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | Axiom of ident
  (* Axiom H ⇓ (Γ, H : P ⊢ Δ, G : P) ≜  [] *)
  | Trivial
  (* Trivial ⇓ (Γ, G : false ⊢ Δ) ≜  [] *)
  (* Trivial ⇓ (Γ ⊢ Δ, G : true ) ≜  [] *)
  | Cut of cterm * certif * certif
  (* Cut (A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ, G : A ⊢ Δ)) *)
  | Split of certif * certif
  (* Split (c₁, c₂) ⇓ (Γ, G : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, G : A ⊢ Δ))  @  (c₂ ⇓ (Γ, G : B ⊢ Δ)) *)
  (* Split (c₁, c₂) ⇓ (Γ ⊢ Δ, G : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ ⊢ Δ, G : B)) *)
  | Unfold of certif
  (* Unfold c ⇓ (Γ, G : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, G : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, G : (A → B) ∧ (B → A)) *)
  (* Unfold c ⇓ (Γ, G : A → B ⊢ Δ) ≜  c ⇓ (Γ, G : ¬A ∨ B ⊢ Δ)*)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A → B) ≜  c ⇓ (Γ ⊢ Δ, G : ¬A ∨ B)*)
  | Swap_neg of certif
  (* Swap_neg c ⇓ (Γ, G : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, G : A)  *)
  (* Swap_neg c ⇓ (Γ, G : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, G : ¬A) *)
  (* Swap_neg c ⇓ (Γ ⊢ Δ, G : A ) ≜  c ⇓ (Γ, G : ¬A ⊢ Δ) *)
  (* Swap_neg c ⇓ (Γ ⊢ Δ, G : ¬A) ≜  c ⇓ (Γ, G : A ⊢ Δ)  *)
  | Destruct of ident * ident * certif
  (* Destruct (H₁, H₂, c) ⇓ (Γ, G : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, H₁ : A, H₂ : B ⊢ Δ) *)
  (* Destruct (H₁, H₂, c) ⇓ (Γ ⊢ Δ, G : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, H₁ : A, H₂ : B) *)
  | Dir of dir * certif
  (* Dir (Left, c) ⇓ (Γ ⊢ Δ, G : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, G : A) *)
  (* Dir (Left, c) ⇓ (Γ, G : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, G : A ⊢ Δ) *)
  (* and similar definition for Right instead of Left *)
  | Weakening of certif
  (* Weakening c ⇓ (Γ ⊢ Δ, G : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening c ⇓ (Γ, G : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Intro_quant of ident * certif
  (* Intro_quant (y, c) ⇓ (Γ, G : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : P y ⊢ Δ) (y fresh) *)
  (* Intro_quant (y, c) ⇓ (Γ ⊢ Δ, G : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : P y) (y fresh) *)
  | Inst_quant of ident * cterm * certif
  (* Inst_quant (H, t, c) ⇓ (Γ, G : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : ∀ x. P x, H : P t ⊢ Δ) *)
  (* Inst_quant (H, t, c) ⇓ (Γ ⊢ Δ, G : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : ∃ x. P x, H : P t) *)
  | Revert of ident * certif (* derived from Inst_quant *)
  (* Revert (x, c) ⇓ (Γ ⊢ Δ, G : P x) ≜  c ⇓ (Γ ⊢ Δ, G : ∀ y. P y) *)
  (* Revert (x, c) ⇓ (Γ, G : P x ⊢ Δ) ≜  c ⇓ (Γ, G : ∃ y. P y ⊢ Δ) *)
  | Rewrite of ident * path * bool * certif list
  (* Rewrite (H, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <G> an equality that is in <H>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)

let skip = Skip, id_register (id_fresh "dummy_skip_ident")

(** Translating a Why3 <task> into a <ctask> *)

let translate_type = function
  | None -> false
  | Some _ -> true

let rec translate_term_rec bv_lvl lvl t =
  { ct_node = translate_term_node_rec bv_lvl lvl t.t_node;
    ct_ty   = translate_type t.t_ty }

and translate_term_node_rec bv_lvl lvl (t_node :term_node) : cterm_node =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  match t_node with
  | Tvar v ->
      let ids = v.vs_name in
      translate_var bv_lvl lvl ids
  | Tapp (ls, lt) ->
      let ids = ls.ls_name in
      let ctapp t1 t2 =
        { ct_node = CTapp (t1, t2);
          ct_ty   = t1.ct_ty && t2.ct_ty } in
      let vs = { ct_node = translate_var bv_lvl lvl ids;
                 ct_ty = translate_type ls.ls_value } in
      (List.fold_left (fun acc t -> ctapp acc (translate_term_rec bv_lvl lvl t))
        vs lt).ct_node
  | Tbinop (op, t1, t2) ->
      let ct1 = translate_term_rec bv_lvl lvl t1 in
      let ct2 = translate_term_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let vs, _, t = t_open_quant tq in
      assert (List.length vs = 1);
      let ids = (List.hd vs).vs_name in
      let lvl = lvl + 1 in
      let ctq = translate_term_rec (Mid.add ids lvl bv_lvl) lvl t in
      CTquant (q, ctq)
  | Tnot t -> CTnot (translate_term_rec bv_lvl lvl t)
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | Tconst _ -> invalid_arg "Cert_syntax.translate_term Tconst"
  | Tif _ -> invalid_arg "Cert_syntax.translate_term Tif"
  | Tlet _ -> invalid_arg "Cert_syntax.translate_term Tlet"
  | Tcase _ -> invalid_arg "Cert_syntax.translate_term Tcase"
  | Teps _ -> invalid_arg "Cert_syntax.translate_term Teps"


and translate_var bv_lvl lvl ids : cterm_node =
  match Mid.find_opt ids bv_lvl with
  | None -> CTfvar ids
  | Some lvl_s ->
      assert (lvl_s <= lvl); (* a variable should not be above its definition *)
      CTbvar (lvl - lvl_s)


let translate_term t = translate_term_rec Mid.empty 0 t

let translate_decl decl =
  match decl.d_node with
  | Dprop (Pgoal, pr, t) ->
       Mid.singleton pr.pr_name (translate_term t, true)
  | Dprop (_, pr, t) ->
      Mid.singleton pr.pr_name (translate_term t, false)
  | _ -> Mid.empty

let translate_tdecl td =
  match td.td_node with
  | Decl decl -> translate_decl decl
  | _ -> Mid.empty

let rec translate_task_acc acc = function
  | Some {task_decl = td; task_prev = task} ->
      let new_acc = Mid.set_union acc (translate_tdecl td) in
      translate_task_acc new_acc task
  | None -> acc

let translate_task task =
  translate_task_acc Mid.empty task


(** Printing of <cterm> and <ctask> : for debugging purposes *)

let ip = create_ident_printer []

let pri fmt i =
  fprintf fmt "%s" (id_unique ip i)
and prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"
and prle sep pre fmt le =
  let prl = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep) pre in
  fprintf fmt "[%a]" prl le

let rec pcte fmt t = match t.ct_node with
  | CTbvar lvl -> pp_print_int fmt lvl
  | CTfvar i -> pri fmt i
  | CTapp (f, arg) -> fprintf fmt "%a@ %a" pcte f pcte arg
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
  | CTquant (q, ct) -> begin match q with
                       | Tforall -> fprintf fmt "∀. %a" pcte ct
                       | Texists -> fprintf fmt "∃. %a" pcte ct
                       end
  | CTnot t -> fprintf fmt "(not %a)" pcte t
  | CTtrue -> fprintf fmt "true"
  | CTfalse -> fprintf fmt "false"
and pro fmt = function
  | Tor -> fprintf fmt "\\/"
  | Tand -> fprintf fmt "/\\"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prr fmt = function
  | Skip -> fprintf fmt "Skip"
  | Axiom h -> fprintf fmt "Axiom@ %a" pri h
  | Trivial -> fprintf fmt "Trivial"
  | Cut (a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a)@]" pcte a prc c1 prc c2
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Unfold c -> fprintf fmt "Unfold@ %a" prc c
  | Swap_neg c -> fprintf fmt "Swap_neg@ %a" prc c
  | Destruct (h1, h2, c) -> fprintf fmt "Destruct @[(%a,@ %a,@ %a)@]"
                              pri h1 pri h2 prc c
  | Dir (d, c) -> fprintf fmt "Dir @[(%a,@ %a)@]" prd d prc c
  | Weakening c -> fprintf fmt "Weakening@ %a" prc c
  | Intro_quant (name, c) -> fprintf fmt "Intro_quant @[(%a,@ %a)@]" pri name prc c
  | Inst_quant (i, t, c) -> fprintf fmt "Inst_quant @[(%a,@ %a,@ %a)@]" pri i pcte t prc c
  | Revert (name, c) -> fprintf fmt "Revert @[(%a,@ %a)@]" pri name prc c
  | Rewrite (h, p, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %b,@ %a)@]"
        pri h (prle "; " prd) p rev (prle "; " prc) lc
and prc fmt (r, g) =
  fprintf fmt "(%a, %a)" prr r pri g


let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prmid fmt mid =
  Mid.iter (fun h (cte, pos) -> fprintf fmt "%a%a : %a\n" prpos pos pri h pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n" prmid cta

let print_ctasks filename lcta =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." (prle "==========\n" pcta) lcta;
  close_out oc


(** We equip existing transformations with a certificate <certif> *)

type ctrans = task -> task list * certif

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(** Create a certified transformation from a transformation with a certificate *)

let checker_ctrans check_certif ctask_equal (ctr : ctrans) task =
  try let (ltask, c) : task list * certif = ctr task in
      let cta = translate_task task in
      print_certif "/tmp/certif.log" c;
      print_ctasks "/tmp/init_ctask.log" [cta];
      let lcta : ctask list = check_certif cta c in
      if Lists.equal ctask_equal lcta (List.map translate_task ltask)
      then ltask
      else begin
          print_ctasks "/tmp/from_trans.log" (List.map translate_task ltask);
          print_ctasks "/tmp/from_cert.log" lcta;
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_ctrans", e))

