(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | mk_ref contents1 => contents1
  end.
Implicit Arguments contents.

Parameter map : forall (a:Type) (b:Type), Type.

Parameter get: forall (a:Type) (b:Type), (map a b) -> a  -> b.

Implicit Arguments get.

Parameter set: forall (a:Type) (b:Type), (map a b) -> a -> b  -> (map a b).

Implicit Arguments set.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b  -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a), ((get (const(
  b1):(map a b)) a1) = b1).

Inductive array (a:Type) :=
  | mk_array : Z -> (map Z a) -> array a.
Implicit Arguments mk_array.

Definition elts (a:Type)(u:(array a)): (map Z a) :=
  match u with
  | mk_array _ elts1 => elts1
  end.
Implicit Arguments elts.

Definition length (a:Type)(u:(array a)): Z :=
  match u with
  | mk_array length1 _ => length1
  end.
Implicit Arguments length.

Definition get1 (a:Type)(a1:(array a)) (i:Z): a := (get (elts a1) i).
Implicit Arguments get1.

Definition set1 (a:Type)(a1:(array a)) (i:Z) (v:a): (array a) :=
  match a1 with
  | mk_array xcl0 _ => (mk_array xcl0 (set (elts a1) i v))
  end.
Implicit Arguments set1.

Definition sorted_sub(a:(map Z Z)) (l:Z) (u:Z): Prop := forall (i1:Z) (i2:Z),
  (((l <= i1)%Z /\ (i1 <= i2)%Z) /\ (i2 <  u)%Z) -> ((get a i1) <= (get a
  i2))%Z.

Definition sorted_sub1(a:(array Z)) (l:Z) (u:Z): Prop := (sorted_sub (elts a)
  l u).

Definition sorted(a:(array Z)): Prop := (sorted_sub (elts a) 0%Z (length a)).

Definition map_eq_sub (a:Type)(a1:(map Z a)) (a2:(map Z a)) (l:Z)
  (u:Z): Prop := forall (i:Z), ((l <= i)%Z /\ (i <  u)%Z) -> ((get a1
  i) = (get a2 i)).
Implicit Arguments map_eq_sub.

Definition exchange (a:Type)(a1:(map Z a)) (a2:(map Z a)) (i:Z)
  (j:Z): Prop := ((get a1 i) = (get a2 j)) /\ (((get a2 i) = (get a1 j)) /\
  forall (k:Z), ((~ (k = i)) /\ ~ (k = j)) -> ((get a1 k) = (get a2 k))).
Implicit Arguments exchange.

Axiom exchange_set : forall (a:Type), forall (a1:(map Z a)), forall (i:Z)
  (j:Z), (exchange a1 (set (set a1 i (get a1 j)) j (get a1 i)) i j).

Inductive permut_sub{a:Type}  : (map Z a) -> (map Z a) -> Z -> Z -> Prop :=
  | permut_refl : forall (a1:(map Z a)) (a2:(map Z a)), forall (l:Z) (u:Z),
      (map_eq_sub a1 a2 l u) -> (permut_sub a1 a2 l u)
  | permut_sym : forall (a1:(map Z a)) (a2:(map Z a)), forall (l:Z) (u:Z),
      (permut_sub a1 a2 l u) -> (permut_sub a2 a1 l u)
  | permut_trans : forall (a1:(map Z a)) (a2:(map Z a)) (a3:(map Z a)),
      forall (l:Z) (u:Z), (permut_sub a1 a2 l u) -> ((permut_sub a2 a3 l
      u) -> (permut_sub a1 a3 l u))
  | permut_exchange : forall (a1:(map Z a)) (a2:(map Z a)), forall (l:Z)
      (u:Z) (i:Z) (j:Z), ((l <= i)%Z /\ (i <  u)%Z) -> (((l <= j)%Z /\
      (j <  u)%Z) -> ((exchange a1 a2 i j) -> (permut_sub a1 a2 l u))).
Implicit Arguments permut_sub.

Axiom permut_weakening : forall (a:Type), forall (a1:(map Z a)) (a2:(map Z
  a)), forall (l1:Z) (r1:Z) (l2:Z) (r2:Z), (((l1 <= l2)%Z /\ (l2 <= r2)%Z) /\
  (r2 <= r1)%Z) -> ((permut_sub a1 a2 l2 r2) -> (permut_sub a1 a2 l1 r1)).

Axiom permut_eq : forall (a:Type), forall (a1:(map Z a)) (a2:(map Z a)),
  forall (l:Z) (u:Z), (permut_sub a1 a2 l u) -> forall (i:Z), ((i <  l)%Z \/
  (u <= i)%Z) -> ((get a2 i) = (get a1 i)).

Axiom permut_exists : forall (a:Type), forall (a1:(map Z a)) (a2:(map Z a)),
  forall (l:Z) (u:Z), (permut_sub a1 a2 l u) -> forall (i:Z), ((l <= i)%Z /\
  (i <  u)%Z) -> exists j:Z, ((l <= j)%Z /\ (j <  u)%Z) /\ ((get a2
  i) = (get a1 j)).

Definition exchange1 (a:Type)(a1:(array a)) (a2:(array a)) (i:Z)
  (j:Z): Prop := (exchange (elts a1) (elts a2) i j).
Implicit Arguments exchange1.

Definition permut_sub1 (a:Type)(a1:(array a)) (a2:(array a)) (l:Z)
  (u:Z): Prop := (permut_sub (elts a1) (elts a2) l u).
Implicit Arguments permut_sub1.

Definition permut (a:Type)(a1:(array a)) (a2:(array a)): Prop :=
  ((length a1) = (length a2)) /\ (permut_sub (elts a1) (elts a2) 0%Z
  (length a1)).
Implicit Arguments permut.

Axiom exchange_permut : forall (a:Type), forall (a1:(array a)) (a2:(array a))
  (i:Z) (j:Z), (exchange1 a1 a2 i j) -> (((length a1) = (length a2)) ->
  (((0%Z <= i)%Z /\ (i <  (length a1))%Z) -> (((0%Z <= j)%Z /\
  (j <  (length a1))%Z) -> (permut a1 a2)))).

Definition array_eq_sub (a:Type)(a1:(array a)) (a2:(array a)) (l:Z)
  (u:Z): Prop := (map_eq_sub (elts a1) (elts a2) l u).
Implicit Arguments array_eq_sub.

Definition array_eq (a:Type)(a1:(array a)) (a2:(array a)): Prop :=
  ((length a1) = (length a2)) /\ (array_eq_sub a1 a2 0%Z (length a1)).
Implicit Arguments array_eq.

Axiom array_eq_sub_permut : forall (a:Type), forall (a1:(array a)) (a2:(array
  a)) (l:Z) (u:Z), (array_eq_sub a1 a2 l u) -> (permut_sub1 a1 a2 l u).

Axiom array_eq_permut : forall (a:Type), forall (a1:(array a)) (a2:(array
  a)), (array_eq a1 a2) -> (permut a1 a2).

Theorem WP_parameter_quick_rec : forall (t:Z), forall (l:Z), forall (r:Z),
  forall (t1:(map Z Z)), ((0%Z <= l)%Z /\ (r <  t)%Z) -> ((l <  r)%Z ->
  (((0%Z <= l)%Z /\ (l <  t)%Z) -> let result := (get t1 l) in
  (((l + 1%Z)%Z <= r)%Z -> forall (m:Z), forall (t2:(map Z Z)),
  ((forall (j:Z), ((l <  j)%Z /\ (j <= m)%Z) -> ((get t2 j) <  result)%Z) /\
  ((forall (j:Z), ((m <  j)%Z /\ (j <  (r + 1%Z)%Z)%Z) -> (result <= (get t2
  j))%Z) /\ ((permut_sub t2 t1 l (r + 1%Z)%Z) /\ (((get t2 l) = result) /\
  ((l <= m)%Z /\ (m <  (r + 1%Z)%Z)%Z))))) -> ((((0%Z <= l)%Z /\
  (l <  t)%Z) /\ ((0%Z <= m)%Z /\ (m <  t)%Z)) -> forall (t3:(map Z Z)),
  (exchange t3 t2 l m) -> ((((0%Z <= ((1%Z + r)%Z - l)%Z)%Z /\
  (((1%Z + (m - 1%Z)%Z)%Z - l)%Z <  ((1%Z + r)%Z - l)%Z)%Z) /\
  ((0%Z <= l)%Z /\ ((m - 1%Z)%Z <  t)%Z)) -> forall (t4:(map Z Z)),
  ((sorted_sub t4 l ((m - 1%Z)%Z + 1%Z)%Z) /\ (permut_sub t4 t3 l
  ((m - 1%Z)%Z + 1%Z)%Z)) -> ((((0%Z <= ((1%Z + r)%Z - l)%Z)%Z /\
  (((1%Z + r)%Z - (m + 1%Z)%Z)%Z <  ((1%Z + r)%Z - l)%Z)%Z) /\
  ((0%Z <= (m + 1%Z)%Z)%Z /\ (r <  t)%Z)) -> forall (t5:(map Z Z)),
  ((sorted_sub t5 (m + 1%Z)%Z (r + 1%Z)%Z) /\ (permut_sub t5 t4 (m + 1%Z)%Z
  (r + 1%Z)%Z)) -> ((sorted_sub t5 l (r + 1%Z)%Z) /\ (permut_sub t5 t1 l
  (r + 1%Z)%Z)))))))).
(* YOU MAY EDIT THE PROOF BELOW *)
intros n l r t1.
intros (hl, hr) hlr hl2 v hlr2.
intros m t2 (inv1, (inv2, (inv3, (inv4, inv5)))).
intros (_, hm) t3 exch.
intros _ t4 (lsorted, lpermut).
intros _ t5 (rsorted, rpermut).
split.
(* sorted *)
red; intros.
assert (h: (l <= i1 < m \/ m <= i1 <= r)%Z) by omega. destruct h.
assert (h: (l <= i2 < m \/ m <= i2 <= r)%Z) by omega. destruct h.
assert (eq: get t4 i1 = get t5 i1).
apply permut_eq with (m+1)%Z (r+1)%Z; auto.
omega.
rewrite <- eq; clear eq.
assert (eq: get t4 i2 = get t5 i2).
apply permut_eq with (m+1)%Z (r+1)%Z; auto.
omega.
rewrite <- eq; clear eq.
apply lsorted; omega.
assert (vi1: (get t5 i1 < v)%Z).
assert (eq: get t4 i1 = get t5 i1).
apply permut_eq with (m+1)%Z (r+1)%Z; auto.
omega.
rewrite <- eq; clear eq.
assert (exists i3:Z, l <= i3 < m-1+1 /\ get t4 i1 = get t3 i3)%Z.
apply permut_exists.
apply permut_sym; auto.
omega.
destruct H2 as (i3, (hi3, eq3)).
rewrite eq3; clear eq3.
assert (case: (i3 = l \/ l < i3)%Z) by omega. destruct case.
subst i3.
destruct exch as (h,_). rewrite h.
apply inv1; omega.
destruct exch as (_,(_,h)). rewrite h; try omega.
apply inv1; omega.
assert (vi2: (v <= get t5 i2)%Z).

(* TODO*) admit. admit. admit.

(* permut *)
apply permut_trans with t4.
apply permut_weakening with (m+1)%Z (r+1)%Z; auto.
omega.
apply permut_trans with t3.
apply permut_weakening with l (m-1+1)%Z; auto.
omega.
apply permut_trans with t2; auto.
apply permut_exchange with l m; auto.
omega.
Qed.
(* DO NOT EDIT BELOW *)


