(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require set.Fset.

(* Why3 goal *)
Definition elt : Type.
Proof.
(* TODO find something more interesting *)
exact Z.
Defined.

(* Why3 goal *)
Definition set : Type.
Proof.
exact (set.Fset.fset elt).
Defined.

(* Why3 goal *)
Definition to_fset : set -> set.Fset.fset elt.
Proof.
exact (fun x => x).
Defined.

(* Why3 goal *)
Definition mk : set.Fset.fset elt -> set.
Proof.
exact (fun x => x).
Defined.

(* Why3 goal *)
Lemma mk'spec : forall (s:set.Fset.fset elt), ((to_fset (mk s)) = s).
Proof.
trivial.
Qed.

(* Why3 goal *)
Definition choose : set -> elt.
Proof.
exact Fset.pick.
Defined.

(* Why3 goal *)
Lemma choose'spec :
  forall (s:set), ~ set.Fset.is_empty (to_fset s) ->
  set.Fset.mem (choose s) (to_fset s).
Proof.
apply Fset.pick_def.
Qed.

