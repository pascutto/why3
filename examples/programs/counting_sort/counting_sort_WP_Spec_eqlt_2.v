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

Parameter map : forall (a:Type) (b:Type), Type.

Parameter get: forall (a:Type) (b:Type), (map a b) -> a -> b.

Implicit Arguments get.

Parameter set: forall (a:Type) (b:Type), (map a b) -> a -> b -> (map a b).

Implicit Arguments set.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a),
  ((get (const b1:(map a b)) a1) = b1).

Inductive array (a:Type) :=
  | mk_array : Z -> (map Z a) -> array a.
Implicit Arguments mk_array.

Definition elts (a:Type)(u:(array a)): (map Z a) :=
  match u with
  | (mk_array _ elts1) => elts1
  end.
Implicit Arguments elts.

Definition length (a:Type)(u:(array a)): Z :=
  match u with
  | (mk_array length1 _) => length1
  end.
Implicit Arguments length.

Definition get1 (a:Type)(a1:(array a)) (i:Z): a := (get (elts a1) i).
Implicit Arguments get1.

Definition set1 (a:Type)(a1:(array a)) (i:Z) (v:a): (array a) :=
  match a1 with
  | (mk_array xcl0 _) => (mk_array xcl0 (set (elts a1) i v))
  end.
Implicit Arguments set1.

Definition sorted_sub(a:(map Z Z)) (l:Z) (u:Z): Prop := forall (i1:Z) (i2:Z),
  (((l <= i1)%Z /\ (i1 <= i2)%Z) /\ (i2 <  u)%Z) -> ((get a i1) <= (get a
  i2))%Z.

Definition sorted_sub1(a:(array Z)) (l:Z) (u:Z): Prop := (sorted_sub (elts a)
  l u).

Definition sorted(a:(array Z)): Prop := (sorted_sub (elts a) 0%Z (length a)).

Parameter k: Z.


Axiom k_positive : (0%Z <  k)%Z.

Definition k_values(a:(array Z)): Prop := forall (i:Z), ((0%Z <= i)%Z /\
  (i <  (length a))%Z) -> ((0%Z <= (get1 a i))%Z /\ ((get1 a i) <  k)%Z).

Definition param  := ((map Z Z)* Z)%type.

Definition eq(p:((map Z Z)* Z)%type) (i:Z): Prop :=
  match p with
  | (a, v) => ((get a i) = v)
  end.

Parameter num_of: ((map Z Z)* Z)%type -> Z -> Z -> Z.


Axiom Num_of_empty : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (b <= a)%Z -> ((num_of p a b) = 0%Z).

Axiom Num_of_right_no_add : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((~ (eq p (b - 1%Z)%Z)) -> ((num_of p a b) = (num_of p a
  (b - 1%Z)%Z))).

Axiom Num_of_right_add : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((eq p (b - 1%Z)%Z) -> ((num_of p a b) = (1%Z + (num_of p a
  (b - 1%Z)%Z))%Z)).

Axiom Num_of_bounds : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((0%Z <= (num_of p a b))%Z /\ ((num_of p a
  b) <= (b - a)%Z)%Z).

Axiom Num_of_append : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z) (c:Z),
  ((a <= b)%Z /\ (b <= c)%Z) -> ((num_of p a c) = ((num_of p a b) + (num_of p
  b c))%Z).

Axiom Num_of_left_no_add : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((~ (eq p a)) -> ((num_of p a b) = (num_of p (a + 1%Z)%Z
  b))).

Axiom Num_of_left_add : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((eq p a) -> ((num_of p a b) = (1%Z + (num_of p (a + 1%Z)%Z
  b))%Z)).

Axiom Empty : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z), (forall (n:Z),
  ((a <= n)%Z /\ (n <  b)%Z) -> ~ (eq p n)) -> ((num_of p a b) = 0%Z).

Axiom Full : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z), (a <  b)%Z ->
  ((forall (n:Z), ((a <= n)%Z /\ (n <  b)%Z) -> (eq p n)) -> ((num_of p a
  b) = (b - a)%Z)).

Axiom num_of_increasing : forall (p:((map Z Z)* Z)%type) (i:Z) (j:Z) (k1:Z),
  ((i <= j)%Z /\ (j <= k1)%Z) -> ((num_of p i j) <= (num_of p i k1))%Z.

Axiom num_of_strictly_increasing : forall (p:((map Z Z)* Z)%type) (i:Z) (j:Z)
  (k1:Z) (l:Z), (((i <= j)%Z /\ (j <= k1)%Z) /\ (k1 <  l)%Z) -> ((eq p k1) ->
  ((num_of p i j) <  (num_of p i l))%Z).

Axiom num_of_change_any : forall (p1:((map Z Z)* Z)%type) (p2:((map Z Z)*
  Z)%type) (a:Z) (b:Z), (forall (j:Z), ((a <= j)%Z /\ (j <  b)%Z) -> ((eq p1
  j) -> (eq p2 j))) -> ((num_of p1 a b) <= (num_of p2 a b))%Z.

Axiom num_of_change_some : forall (p1:((map Z Z)* Z)%type) (p2:((map Z Z)*
  Z)%type) (a:Z) (b:Z) (i:Z), ((a <= i)%Z /\ (i <  b)%Z) -> ((forall (j:Z),
  ((a <= j)%Z /\ (j <  b)%Z) -> ((eq p1 j) -> (eq p2 j))) -> ((~ (eq p1
  i)) -> ((eq p2 i) -> ((num_of p1 a b) <  (num_of p2 a b))%Z))).

Definition numeq(a:(array Z)) (v:Z) (i:Z) (j:Z): Z := (num_of ((elts a), v) i
  j).

Definition lt(p:((map Z Z)* Z)%type) (i:Z): Prop :=
  match p with
  | (a, v) => ((get a i) <  v)%Z
  end.

Parameter num_of1: ((map Z Z)* Z)%type -> Z -> Z -> Z.


Axiom Num_of_empty1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (b <= a)%Z -> ((num_of1 p a b) = 0%Z).

Axiom Num_of_right_no_add1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((~ (lt p (b - 1%Z)%Z)) -> ((num_of1 p a b) = (num_of1 p a
  (b - 1%Z)%Z))).

Axiom Num_of_right_add1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((lt p (b - 1%Z)%Z) -> ((num_of1 p a b) = (1%Z + (num_of1 p a
  (b - 1%Z)%Z))%Z)).

Axiom Num_of_bounds1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((0%Z <= (num_of1 p a b))%Z /\ ((num_of1 p a
  b) <= (b - a)%Z)%Z).

Axiom Num_of_append1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z) (c:Z),
  ((a <= b)%Z /\ (b <= c)%Z) -> ((num_of1 p a c) = ((num_of1 p a
  b) + (num_of1 p b c))%Z).

Axiom Num_of_left_no_add1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((~ (lt p a)) -> ((num_of1 p a b) = (num_of1 p (a + 1%Z)%Z
  b))).

Axiom Num_of_left_add1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z),
  (a <  b)%Z -> ((lt p a) -> ((num_of1 p a b) = (1%Z + (num_of1 p (a + 1%Z)%Z
  b))%Z)).

Axiom Empty1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z), (forall (n:Z),
  ((a <= n)%Z /\ (n <  b)%Z) -> ~ (lt p n)) -> ((num_of1 p a b) = 0%Z).

Axiom Full1 : forall (p:((map Z Z)* Z)%type) (a:Z) (b:Z), (a <  b)%Z ->
  ((forall (n:Z), ((a <= n)%Z /\ (n <  b)%Z) -> (lt p n)) -> ((num_of1 p a
  b) = (b - a)%Z)).

Axiom num_of_increasing1 : forall (p:((map Z Z)* Z)%type) (i:Z) (j:Z) (k1:Z),
  ((i <= j)%Z /\ (j <= k1)%Z) -> ((num_of1 p i j) <= (num_of1 p i k1))%Z.

Axiom num_of_strictly_increasing1 : forall (p:((map Z Z)* Z)%type) (i:Z)
  (j:Z) (k1:Z) (l:Z), (((i <= j)%Z /\ (j <= k1)%Z) /\ (k1 <  l)%Z) -> ((lt p
  k1) -> ((num_of1 p i j) <  (num_of1 p i l))%Z).

Axiom num_of_change_any1 : forall (p1:((map Z Z)* Z)%type) (p2:((map Z Z)*
  Z)%type) (a:Z) (b:Z), (forall (j:Z), ((a <= j)%Z /\ (j <  b)%Z) -> ((lt p1
  j) -> (lt p2 j))) -> ((num_of1 p1 a b) <= (num_of1 p2 a b))%Z.

Axiom num_of_change_some1 : forall (p1:((map Z Z)* Z)%type) (p2:((map Z Z)*
  Z)%type) (a:Z) (b:Z) (i:Z), ((a <= i)%Z /\ (i <  b)%Z) -> ((forall (j:Z),
  ((a <= j)%Z /\ (j <  b)%Z) -> ((lt p1 j) -> (lt p2 j))) -> ((~ (lt p1
  i)) -> ((lt p2 i) -> ((num_of1 p1 a b) <  (num_of1 p2 a b))%Z))).

Definition numlt(a:(array Z)) (v:Z) (i:Z) (j:Z): Z := (num_of1 ((elts a), v)
  i j).

(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem eqlt : forall (a:(array Z)), (k_values a) -> forall (v:Z),
  ((0%Z <= v)%Z /\ (v <  k)%Z) -> forall (l:Z) (u:Z), (((0%Z <= l)%Z /\
  (l <  u)%Z) /\ (u <= (length a))%Z) -> (((numlt a v l u) + (numeq a v l
  u))%Z = (numlt a (v + 1%Z)%Z l u)).
(* YOU MAY EDIT THE PROOF BELOW *)
intros (n,m); simpl.
intros ha v hv l u hu.
unfold numlt, numeq; simpl.
generalize hu; pattern u; apply natlike_ind; intuition.
red in ha. unfold get1 in ha. simpl in ha.
assert (case: (get m x < v \/ get m x = v \/ get m x > v)%Z) by omega. destruct case.
rewrite Num_of_right_add1; try omega.
rewrite Num_of_right_no_add.
rewrite Num_of_right_add1 with (b:=(Zsucc x)); try omega.

assert (case: (l < x \/ x <= l)%Z) by omega. destruct case.
ring_simplify.
replace (x+1-1)%Z with x by omega.
generalize (H6 H10); intuition.
rewrite Num_of_empty; try omega.
rewrite Num_of_empty1; try omega.
rewrite Num_of_empty1; try omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
omega.
omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
intro; omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
assumption.

destruct H5.
rewrite Num_of_right_no_add1; try omega.
rewrite Num_of_right_add.
rewrite Num_of_right_add1 with (b:=(Zsucc x)); try omega.
assert (case: (l < x \/ x <= l)%Z) by omega. destruct case.
ring_simplify.
replace (x+1-1)%Z with x by omega.
generalize (H6 H10); intuition.
rewrite Num_of_empty; try omega.
rewrite Num_of_empty1; try omega.
rewrite Num_of_empty1; try omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
omega.
omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
assumption.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
intro; omega.

rewrite Num_of_right_no_add1; try omega.
rewrite Num_of_right_no_add; try omega.
rewrite Num_of_right_no_add1 with (b:=(Zsucc x)); try omega.
assert (case: (l < x \/ x <= l)%Z) by omega. destruct case.
replace (Zsucc x-1)%Z with x by omega.
apply H6; omega.
rewrite Num_of_empty; try omega.
rewrite Num_of_empty1; try omega.
rewrite Num_of_empty1; try omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
omega.
red; simpl.
replace (Zsucc x - 1)%Z with x by omega.
omega.

Qed.
(* DO NOT EDIT BELOW *)


