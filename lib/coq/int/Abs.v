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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

(* Why3 comment *)
(* abs is replaced with (ZArith.BinInt.Z.abs x) by the coq driver *)

(* Why3 goal *)
Lemma abs_def :
  forall (x:Z),
  ((0%Z <= x)%Z -> ((ZArith.BinInt.Z.abs x) = x)) /\
  (~ (0%Z <= x)%Z -> ((ZArith.BinInt.Z.abs x) = (-x)%Z)).
intros x.
split ; intros H.
now apply Zabs_eq.
apply Zabs_non_eq.
apply Znot_gt_le.
contradict H.
apply Zlt_le_weak.
now apply Zgt_lt.
Qed.

(* Why3 goal *)
Lemma Abs_le :
  forall (x:Z) (y:Z),
  ((ZArith.BinInt.Z.abs x) <= y)%Z <-> (((-y)%Z <= x)%Z /\ (x <= y)%Z).
intros x y.
zify.
omega.
Qed.

(* Why3 goal *)
Lemma Abs_pos : forall (x:Z), (0%Z <= (ZArith.BinInt.Z.abs x))%Z.
exact Zabs_pos.
Qed.

