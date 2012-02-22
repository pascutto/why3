(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require int.Int.
Definition unit  := unit.

Parameter qtmark : Type.

Parameter at1: forall (a:Type), a -> qtmark -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a -> a.

Implicit Arguments old.

Definition implb(x:bool) (y:bool): bool := match (x,
  y) with
  | (true, false) => false
  | (_, _) => true
  end.

Parameter set : forall (a:Type), Type.

Parameter mem: forall (a:Type), a -> (set a) -> Prop.

Implicit Arguments mem.

Definition infix_eqeq (a:Type)(s1:(set a)) (s2:(set a)): Prop :=
  forall (x:a), (mem x s1) <-> (mem x s2).
Implicit Arguments infix_eqeq.

Axiom extensionality : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (infix_eqeq s1 s2) -> (s1 = s2).

Definition subset (a:Type)(s1:(set a)) (s2:(set a)): Prop := forall (x:a),
  (mem x s1) -> (mem x s2).
Implicit Arguments subset.

Axiom subset_trans : forall (a:Type), forall (s1:(set a)) (s2:(set a))
  (s3:(set a)), (subset s1 s2) -> ((subset s2 s3) -> (subset s1 s3)).

Parameter empty: forall (a:Type), (set a).

Set Contextual Implicit.
Implicit Arguments empty.
Unset Contextual Implicit.

Definition is_empty (a:Type)(s:(set a)): Prop := forall (x:a), ~ (mem x s).
Implicit Arguments is_empty.

Axiom empty_def1 : forall (a:Type), (is_empty (empty:(set a))).

Parameter add: forall (a:Type), a -> (set a) -> (set a).

Implicit Arguments add.

Axiom add_def1 : forall (a:Type), forall (x:a) (y:a), forall (s:(set a)),
  (mem x (add y s)) <-> ((x = y) \/ (mem x s)).

Parameter remove: forall (a:Type), a -> (set a) -> (set a).

Implicit Arguments remove.

Axiom remove_def1 : forall (a:Type), forall (x:a) (y:a) (s:(set a)), (mem x
  (remove y s)) <-> ((~ (x = y)) /\ (mem x s)).

Axiom subset_remove : forall (a:Type), forall (x:a) (s:(set a)),
  (subset (remove x s) s).

Parameter union: forall (a:Type), (set a) -> (set a) -> (set a).

Implicit Arguments union.

Axiom union_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (union s1 s2)) <-> ((mem x s1) \/ (mem x s2)).

Parameter inter: forall (a:Type), (set a) -> (set a) -> (set a).

Implicit Arguments inter.

Axiom inter_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (inter s1 s2)) <-> ((mem x s1) /\ (mem x s2)).

Parameter diff: forall (a:Type), (set a) -> (set a) -> (set a).

Implicit Arguments diff.

Axiom diff_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (diff s1 s2)) <-> ((mem x s1) /\ ~ (mem x s2)).

Axiom subset_diff : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (subset (diff s1 s2) s1).

Parameter cardinal: forall (a:Type), (set a) -> Z.

Implicit Arguments cardinal.

Axiom cardinal_nonneg : forall (a:Type), forall (s:(set a)),
  (0%Z <= (cardinal s))%Z.

Axiom cardinal_empty : forall (a:Type), forall (s:(set a)),
  ((cardinal s) = 0%Z) <-> (is_empty s).

Axiom cardinal_add : forall (a:Type), forall (x:a), forall (s:(set a)),
  (~ (mem x s)) -> ((cardinal (add x s)) = (1%Z + (cardinal s))%Z).

Axiom cardinal_remove : forall (a:Type), forall (x:a), forall (s:(set a)),
  (mem x s) -> ((cardinal s) = (1%Z + (cardinal (remove x s)))%Z).

Axiom cardinal_subset : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (subset s1 s2) -> ((cardinal s1) <= (cardinal s2))%Z.

Parameter vertex : Type.

Parameter succ: vertex -> (set vertex).


Inductive path : vertex -> vertex -> Z -> Prop :=
  | path_empty : forall (v:vertex), (path v v 0%Z)
  | path_succ : forall (v1:vertex) (v2:vertex) (v3:vertex) (n:Z), (path v1 v2
      n) -> ((mem v3 (succ v2)) -> (path v1 v3 (n + 1%Z)%Z)).

Axiom path_nonneg : forall (v1:vertex) (v2:vertex) (n:Z), (path v1 v2 n) ->
  (0%Z <= n)%Z.

Axiom path_inversion : forall (v1:vertex) (v3:vertex) (n:Z), (0%Z <= n)%Z ->
  ((path v1 v3 (n + 1%Z)%Z) -> exists v2:vertex, (path v1 v2 n) /\ (mem v3
  (succ v2))).

Axiom path_closure : forall (s:(set vertex)), (forall (x:vertex), (mem x
  s) -> forall (y:vertex), (mem y (succ x)) -> (mem y s)) ->
  forall (v1:vertex) (v2:vertex) (n:Z), (path v1 v2 n) -> ((mem v1 s) ->
  (mem v2 s)).

Definition shortest_path(v1:vertex) (v2:vertex) (n:Z): Prop := (path v1 v2
  n) /\ forall (m:Z), (m <  n)%Z -> ~ (path v1 v2 m).

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | (mk_ref contents1) => contents1
  end.
Implicit Arguments contents.

Definition bag (a:Type) := (ref (set a)).

Definition inv(s:vertex) (t:vertex) (visited:(set vertex)) (current:(set
  vertex)) (next:(set vertex)) (d:Z): Prop := (subset current visited) /\
  ((forall (x:vertex), (mem x current) -> (shortest_path s x d)) /\
  ((subset next visited) /\ ((forall (x:vertex), (mem x next) ->
  (shortest_path s x (d + 1%Z)%Z)) /\ ((forall (x:vertex) (m:Z), (path s x
  m) -> ((m <= d)%Z -> (mem x visited))) /\ ((forall (x:vertex), (mem x
  visited) -> exists m:Z, (path s x m) /\ (m <= (d + 1%Z)%Z)%Z) /\
  ((forall (x:vertex), (shortest_path s x (d + 1%Z)%Z) -> ((mem x next) \/
  ~ (mem x visited))) /\ ((mem t visited) -> ((mem t current) \/ (mem t
  next))))))))).

Definition closure(visited:(set vertex)) (current:(set vertex)) (next:(set
  vertex)) (x:vertex): Prop := (mem x visited) -> ((~ (mem x current)) ->
  ((~ (mem x next)) -> forall (y:vertex), (mem y (succ x)) -> (mem y
  visited))).

(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem WP_parameter_bfs : forall (s:vertex), forall (t:vertex),
  forall (d:Z), forall (next:(set vertex)), forall (current:(set vertex)),
  forall (visited:(set vertex)), ((inv s t visited current next d) /\
  (((is_empty current) -> (is_empty next)) /\ ((forall (x:vertex),
  (closure visited current next x)) /\ (0%Z <= d)%Z))) ->
  forall (result:bool), ((result = true) <-> (is_empty current)) ->
  ((result = true) -> ((~ (mem t visited)) -> forall (d1:Z), ~ (path s t
  d1))).
(* YOU MAY EDIT THE PROOF BELOW *)
intuition.
assert (mem t visited).
apply path_closure with s d1; auto.
unfold closure in H1.
intros x hx.
apply H1; intuition.
apply (H2 x); auto.
apply (H6 x); auto.
red in H0; decompose [and] H0.
apply H12 with 0%Z.
apply path_empty.
assumption.
exact (H5 H8).
Qed.
(* DO NOT EDIT BELOW *)


