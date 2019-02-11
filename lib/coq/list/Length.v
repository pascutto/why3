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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require list.List.

(* Why3 assumption *)
Fixpoint length {a:Type} {a_WT:WhyType a} (l:(list a)) {struct l}: Z :=
  match l with
  | Init.Datatypes.nil => 0%Z
  | (Init.Datatypes.cons _ r) => (1%Z + (length r))%Z
  end.

Lemma length_std :
  forall {a:Type} {a_WT:WhyType a} (l:list a),
  length l = Z_of_nat (List.length l).
Proof.
intros a a_WT l.
induction l.
easy.
change (1 + length l = Z_of_nat (S (List.length l)))%Z.
now rewrite inj_S, Zplus_comm, IHl.
Qed.

(* Why3 goal *)
Lemma Length_nonnegative {a:Type} {a_WT:WhyType a} :
  forall (l:(list a)), (0%Z <= (length l))%Z.
Proof.
intros l.
rewrite length_std.
apply Zle_0_nat.
Qed.

(* Why3 goal *)
Lemma Length_nil {a:Type} {a_WT:WhyType a} :
  forall (l:(list a)), ((length l) = 0%Z) <-> (l = Init.Datatypes.nil).
Proof.
intros [|h t] ; split ; try easy.
unfold length. fold length.
intros H.
exfalso.
generalize (Length_nonnegative t).
omega.
Qed.

