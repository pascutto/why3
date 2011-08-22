(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require Import ZOdiv.
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Axiom Abs_pos : forall (x:Z), (0%Z <= (Zabs x))%Z.

Axiom Div_mod : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  (x = ((y * (ZOdiv x y))%Z + (ZOmod x y))%Z).

Axiom Div_bound : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <  y)%Z) ->
  ((0%Z <= (ZOdiv x y))%Z /\ ((ZOdiv x y) <= x)%Z).

Axiom Mod_bound : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  (((-(Zabs y))%Z <  (ZOmod x y))%Z /\ ((ZOmod x y) <  (Zabs y))%Z).

Axiom Div_sign_pos : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <  y)%Z) ->
  (0%Z <= (ZOdiv x y))%Z.

Axiom Div_sign_neg : forall (x:Z) (y:Z), ((x <= 0%Z)%Z /\ (0%Z <  y)%Z) ->
  ((ZOdiv x y) <= 0%Z)%Z.

Axiom Mod_sign_pos : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ ~ (y = 0%Z)) ->
  (0%Z <= (ZOmod x y))%Z.

Axiom Mod_sign_neg : forall (x:Z) (y:Z), ((x <= 0%Z)%Z /\ ~ (y = 0%Z)) ->
  ((ZOmod x y) <= 0%Z)%Z.

Axiom Rounds_toward_zero : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  ((Zabs ((ZOdiv x y) * y)%Z) <= (Zabs x))%Z.

Axiom Div_1 : forall (x:Z), ((ZOdiv x 1%Z) = x).

Axiom Mod_1 : forall (x:Z), ((ZOmod x 1%Z) = 0%Z).

Axiom Div_inf : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (x <  y)%Z) ->
  ((ZOdiv x y) = 0%Z).

Axiom Mod_inf : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (x <  y)%Z) ->
  ((ZOmod x y) = x).

Axiom Div_mult : forall (x:Z) (y:Z) (z:Z), ((0%Z <  x)%Z /\ ((0%Z <= y)%Z /\
  (0%Z <= z)%Z)) -> ((ZOdiv ((x * y)%Z + z)%Z x) = (y + (ZOdiv z x))%Z).

Axiom Mod_mult : forall (x:Z) (y:Z) (z:Z), ((0%Z <  x)%Z /\ ((0%Z <= y)%Z /\
  (0%Z <= z)%Z)) -> ((ZOmod ((x * y)%Z + z)%Z x) = (ZOmod z x)).

Definition left(i:Z): Z := ((2%Z * i)%Z + 1%Z)%Z.

Definition right(i:Z): Z := ((2%Z * i)%Z + 2%Z)%Z.

Definition parent(i:Z): Z := (ZOdiv (i - 1%Z)%Z 2%Z).

Axiom Parent_inf : forall (i:Z), (0%Z <  i)%Z -> ((parent i) <  i)%Z.

Axiom Left_sup : forall (i:Z), (0%Z <= i)%Z -> (i <  (left i))%Z.

Axiom Right_sup : forall (i:Z), (0%Z <= i)%Z -> (i <  (right i))%Z.

Axiom Parent_right : forall (i:Z), (0%Z <= i)%Z -> ((parent (right i)) = i).

Axiom Parent_left : forall (i:Z), (0%Z <= i)%Z -> ((parent (left i)) = i).

Axiom Inf_parent : forall (i:Z) (j:Z), ((0%Z <  j)%Z /\
  (j <= (right i))%Z) -> ((parent j) <= i)%Z.

Axiom Child_parent : forall (i:Z), (0%Z <  i)%Z ->
  ((i = (left (parent i))) \/ (i = (right (parent i)))).

Axiom Parent_pos : forall (j:Z), (0%Z <  j)%Z -> (0%Z <= (parent j))%Z.

Definition parentChild(i:Z) (j:Z): Prop := ((0%Z <= i)%Z /\ (i <  j)%Z) ->
  ((j = (left i)) \/ (j = (right i))).

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

Definition map1  := (map Z Z).

Definition logic_heap  := ((map Z Z)* Z)%type.

Definition is_heap_array(a:(map Z Z)) (idx:Z) (sz:Z): Prop :=
  (0%Z <= idx)%Z -> forall (i:Z) (j:Z), (((idx <= i)%Z /\ (i <  j)%Z) /\
  (j <  sz)%Z) -> ((parentChild i j) -> ((get a i) <= (get a j))%Z).

Definition is_heap(h:((map Z Z)* Z)%type): Prop :=
  match h with
  | (a, sz) => (0%Z <= sz)%Z /\ (is_heap_array a 0%Z sz)
  end.

Axiom Is_heap_when_no_element : forall (a:(map Z Z)) (idx:Z) (n:Z),
  ((0%Z <= n)%Z /\ (n <= idx)%Z) -> (is_heap_array a idx n).

Axiom Is_heap_sub : forall (a:(map Z Z)) (i:Z) (n:Z), (is_heap_array a i
  n) -> forall (j:Z), ((i <= j)%Z /\ (j <= n)%Z) -> (is_heap_array a i j).

Axiom Is_heap_sub2 : forall (a:(map Z Z)) (n:Z), (is_heap_array a 0%Z n) ->
  forall (j:Z), ((0%Z <= j)%Z /\ (j <= n)%Z) -> (is_heap_array a j n).

Axiom Is_heap_when_node_modified : forall (a:(map Z Z)) (n:Z) (e:Z) (idx:Z),
  (is_heap_array a idx n) -> forall (i:Z), ((0%Z <= i)%Z /\ (i <  n)%Z) ->
  (((0%Z <  i)%Z -> ((get a (parent i)) <= e)%Z) -> ((((left i) <  n)%Z ->
  (e <= (get a (left i)))%Z) -> ((((right i) <  n)%Z -> (e <= (get a
  (right i)))%Z) -> (is_heap_array (set a i e) idx n)))).

Axiom Is_heap_add_last : forall (a:(map Z Z)) (n:Z) (e:Z), (0%Z <  n)%Z ->
  (((is_heap_array a 0%Z n) /\ ((get a (parent n)) <= e)%Z) ->
  (is_heap_array (set a n e) 0%Z (n + 1%Z)%Z)).

Axiom Parent_inf_el : forall (a:(map Z Z)) (n:Z), (is_heap_array a 0%Z n) ->
  forall (j:Z), ((0%Z <  j)%Z /\ (j <  n)%Z) -> ((get a (parent j)) <= (get a
  j))%Z.

Axiom Left_sup_el : forall (a:(map Z Z)) (n:Z), (is_heap_array a 0%Z n) ->
  forall (j:Z), ((0%Z <= j)%Z /\ (j <  n)%Z) -> (((left j) <  n)%Z -> ((get a
  j) <= (get a (left j)))%Z).

Axiom Right_sup_el : forall (a:(map Z Z)) (n:Z), (is_heap_array a 0%Z n) ->
  forall (j:Z), ((0%Z <= j)%Z /\ (j <  n)%Z) -> (((right j) <  n)%Z ->
  ((get a j) <= (get a (right j)))%Z).

Axiom Is_heap_relation : forall (a:(map Z Z)) (n:Z), (0%Z <  n)%Z ->
  ((is_heap_array a 0%Z n) -> forall (j:Z), (0%Z <= j)%Z -> ((j <  n)%Z ->
  ((get a 0%Z) <= (get a j))%Z)).

Definition bag (a:Type) := (map a Z).

Axiom occ_non_negative : forall (a:Type), forall (b:(map a Z)) (x:a),
  (0%Z <= (get b x))%Z.

Definition eq_bag (a:Type)(a1:(map a Z)) (b:(map a Z)): Prop := forall (x:a),
  ((get a1 x) = (get b x)).
Implicit Arguments eq_bag.

Axiom bag_extensionality : forall (a:Type), forall (a1:(map a Z)) (b:(map a
  Z)), (eq_bag a1 b) -> (a1 = b).

Parameter empty_bag: forall (a:Type),  (map a Z).

Set Contextual Implicit.
Implicit Arguments empty_bag.
Unset Contextual Implicit.

Axiom occ_empty : forall (a:Type), forall (x:a), ((get (empty_bag:(map a Z))
  x) = 0%Z).

Axiom is_empty : forall (a:Type), forall (b:(map a Z)), (forall (x:a),
  ((get b x) = 0%Z)) -> (b = (empty_bag:(map a Z))).

Axiom occ_singleton_eq : forall (a:Type), forall (x:a) (y:a), (x = y) ->
  ((get (set (empty_bag:(map a Z)) x 1%Z) y) = 1%Z).

Axiom occ_singleton_neq : forall (a:Type), forall (x:a) (y:a), (~ (x = y)) ->
  ((get (set (empty_bag:(map a Z)) x 1%Z) y) = 0%Z).

Parameter union: forall (a:Type), (map a Z) -> (map a Z)  -> (map a Z).

Implicit Arguments union.

Axiom occ_union : forall (a:Type), forall (x:a) (a1:(map a Z)) (b:(map a Z)),
  ((get (union a1 b) x) = ((get a1 x) + (get b x))%Z).

Axiom Union_comm : forall (a:Type), forall (a1:(map a Z)) (b:(map a Z)),
  ((union a1 b) = (union b a1)).

Axiom Union_identity : forall (a:Type), forall (a1:(map a Z)), ((union a1
  (empty_bag:(map a Z))) = a1).

Axiom Union_assoc : forall (a:Type), forall (a1:(map a Z)) (b:(map a Z))
  (c:(map a Z)), ((union a1 (union b c)) = (union (union a1 b) c)).

Axiom bag_simpl : forall (a:Type), forall (a1:(map a Z)) (b:(map a Z))
  (c:(map a Z)), ((union a1 b) = (union c b)) -> (a1 = c).

Definition add (a:Type)(x:a) (b:(map a Z)): (map a Z) :=
  (union (set (empty_bag:(map a Z)) x 1%Z) b).
Implicit Arguments add.

Axiom occ_add_eq : forall (a:Type), forall (b:(map a Z)) (x:a) (y:a),
  (x = y) -> ((get (add x b) x) = ((get b x) + 1%Z)%Z).

Axiom occ_add_neq : forall (a:Type), forall (b:(map a Z)) (x:a) (y:a),
  (~ (x = y)) -> ((get (add x b) y) = (get b y)).

Parameter card: forall (a:Type), (map a Z)  -> Z.

Implicit Arguments card.

Axiom Card_empty : forall (a:Type), ((card (empty_bag:(map a Z))) = 0%Z).

Axiom Card_singleton : forall (a:Type), forall (x:a),
  ((card (set (empty_bag:(map a Z)) x 1%Z)) = 1%Z).

Axiom Card_union : forall (a:Type), forall (x:(map a Z)) (y:(map a Z)),
  ((card (union x y)) = ((card x) + (card y))%Z).

Axiom Card_zero_empty : forall (a:Type), forall (x:(map a Z)),
  ((card x) = 0%Z) -> (x = (empty_bag:(map a Z))).

Definition array (a:Type) := (map Z a).

Parameter elements: forall (a:Type), (map Z a) -> Z -> Z  -> (map a Z).

Implicit Arguments elements.

Axiom Elements_empty : forall (a:(map Z Z)) (i:Z) (j:Z), (j <= i)%Z ->
  ((elements a i j) = (empty_bag:(map Z Z))).

Axiom Elements_singleton : forall (a:(map Z Z)) (i:Z) (j:Z),
  (j = (i + 1%Z)%Z) -> ((elements a i j) = (set (empty_bag:(map Z Z)) (get a
  i) 1%Z)).

Axiom Elements_union : forall (a:(map Z Z)) (i:Z) (j:Z) (k:Z), ((i <= j)%Z /\
  (j <= k)%Z) -> ((elements a i k) = (union (elements a i j) (elements a j
  k))).

Axiom Elements_union1 : forall (a:(map Z Z)) (i:Z) (j:Z), (i <  j)%Z ->
  ((elements a i j) = (add (get a i) (elements a (i + 1%Z)%Z j))).

Axiom Elements_union2 : forall (a:(map Z Z)) (i:Z) (j:Z), (i <  j)%Z ->
  ((elements a i j) = (add (get a (j - 1%Z)%Z) (elements a i (j - 1%Z)%Z))).

Axiom Elements_set : forall (a:(map Z Z)) (i:Z) (j:Z), (i <= j)%Z ->
  forall (k:Z), ((k <  i)%Z \/ (j <= k)%Z) -> forall (e:Z), ((elements (set a
  k e) i j) = (elements a i j)).

Axiom Elements_union3 : forall (a:(map Z Z)) (i:Z) (j:Z) (k:Z), (i <= j)%Z ->
  ((add k (elements a i j)) = (elements (set a j k) i (j + 1%Z)%Z)).

Axiom Elements_set2 : forall (a:(map Z Z)) (i:Z) (j:Z) (k:Z), ((i <= k)%Z /\
  (k <  j)%Z) -> forall (e:Z), ((add (get a k) (elements (set a k e) i
  j)) = (add e (elements a i j))).

Definition model(h:((map Z Z)* Z)%type): (map Z Z) :=
  match h with
  | (a, n) => (elements a 0%Z n)
  end.

Axiom Model_empty : forall (a:(map Z Z)), ((model (a, 0%Z)) = (empty_bag:(map
  Z Z))).

Axiom Model_singleton : forall (a:(map Z Z)), ((model (a,
  1%Z)) = (set (empty_bag:(map Z Z)) (get a 0%Z) 1%Z)).

Axiom Model_set : forall (a:(map Z Z)) (aqt:(map Z Z)) (v:Z) (i:Z) (n:Z),
  ((0%Z <= i)%Z /\ (i <  n)%Z) -> ((aqt = (set a i v)) -> ((add (get a i)
  (model (aqt, n))) = (add v (model (a, n))))).

Axiom Model_add_last : forall (a:(map Z Z)) (n:Z), (0%Z <= n)%Z -> ((model (
  a, (n + 1%Z)%Z)) = (add (get a n) (model (a, n)))).

Parameter min: Z -> Z  -> Z.


Parameter max: Z -> Z  -> Z.


Axiom Max_is_ge : forall (x:Z) (y:Z), (x <= (max x y))%Z /\ (y <= (max x
  y))%Z.

Axiom Max_is_some : forall (x:Z) (y:Z), ((max x y) = x) \/ ((max x y) = y).

Axiom Min_is_le : forall (x:Z) (y:Z), ((min x y) <= x)%Z /\ ((min x
  y) <= y)%Z.

Axiom Min_is_some : forall (x:Z) (y:Z), ((min x y) = x) \/ ((min x y) = y).

Axiom Max_x : forall (x:Z) (y:Z), (y <= x)%Z -> ((max x y) = x).

Axiom Max_y : forall (x:Z) (y:Z), (x <= y)%Z -> ((max x y) = y).

Axiom Min_x : forall (x:Z) (y:Z), (x <= y)%Z -> ((min x y) = x).

Axiom Min_y : forall (x:Z) (y:Z), (y <= x)%Z -> ((min x y) = y).

Axiom Max_sym : forall (x:Z) (y:Z), (y <= x)%Z -> ((max x y) = (max y x)).

Axiom Min_sym : forall (x:Z) (y:Z), (y <= x)%Z -> ((min x y) = (min y x)).

Parameter min_bag: (map Z Z)  -> Z.


Axiom Min_bag_singleton : forall (x:Z), ((min_bag (set (empty_bag:(map Z Z))
  x 1%Z)) = x).

Axiom Min_bag_union : forall (x:(map Z Z)) (y:(map Z Z)), ((min_bag (union x
  y)) = (min (min_bag x) (min_bag y))).

Axiom Min_bag_union1 : forall (x:(map Z Z)) (y:(map Z Z)) (a:Z), (x = (add a
  y)) -> ((min_bag x) = (min a (min_bag y))).

Axiom Min_bag_union2 : forall (x:(map Z Z)) (a:Z), (a <= (min_bag x))%Z ->
  (a <= (min_bag (add a x)))%Z.

Axiom Is_heap_min : forall (a:(map Z Z)) (n:Z), (0%Z <  n)%Z ->
  ((is_heap_array a 0%Z n) -> ((get a 0%Z) = (min_bag (model (a, n))))).

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | mk_ref contents1 => contents1
  end.
Implicit Arguments contents.

(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem WP_parameter_insert : forall (e:Z), forall (this:(map Z Z))
  (this1:Z), (is_heap (this, this1)) -> forall (i:Z), forall (arr:(map Z Z)),
  (((0%Z <= i)%Z /\ (i <= this1)%Z) /\ (((i = this1) -> ((is_heap_array arr
  0%Z this1) /\ ((elements arr 0%Z this1) = (elements this 0%Z this1)))) /\
  ((i <  this1)%Z -> ((is_heap_array arr 0%Z (this1 + 1%Z)%Z) /\
  ((e <  (get arr i))%Z /\ ((elements arr 0%Z
  (this1 + 1%Z)%Z) = (add (get arr i) (elements this 0%Z this1)))))))) ->
  ((0%Z <  i)%Z -> ((~ ((get arr (ZOdiv (i - 1%Z)%Z 2%Z)) <= e)%Z) ->
  forall (arr1:(map Z Z)), (arr1 = (set arr i (get arr
  (ZOdiv (i - 1%Z)%Z 2%Z)))) -> forall (i1:Z),
  (i1 = (ZOdiv (i - 1%Z)%Z 2%Z)) -> ((i1 <  this1)%Z -> ((elements arr1 0%Z
  (this1 + 1%Z)%Z) = (add (get arr1 i1) (elements this 0%Z this1)))))).
(* YOU MAY EDIT THE PROOF BELOW *)
intros e a n H_heap.
intros  i a0 (H_i, (H1, H2)).
intro H_i_pos.
intro H_e.
intros a1 Ha1.
intros i1 Hi1; subst i1.
intros Hipar.
assert (h: i = n \/ i < n) by omega.
   destruct h.
   (*case i = n*)
   clear H2; elim (H1 H); intros _ H2.
   rewrite <- H2; clear H2.
   subst i.
   pattern (add (get a1 ((n - 1) / 2)) (elements a0 0 n)); 
     rewrite Elements_union3; auto with *.
   subst a1; rewrite Select_neq; auto with zarith.
   (*case i < n*)
   elim (H2 H); clear H1 H2; intros _ (_,H3).
   subst a1; rewrite Select_neq.
   assert (h:(0 <= i < n+1)) by omega.
   generalize (Elements_set2 a0 0 (n+1) i h (get a0 ((i - 1) / 2))); clear h; intro h.
   (* we add {a[i]} to both side of the equality *)
   apply bag_simpl with (b:= (set empty_bag (get a0 i) 1)).
   unfold add in *.
   rewrite Union_comm.
   rewrite h; clear h.
   rewrite H3; clear H3.
   (* AC equality *)
   pattern (union (set empty_bag (get a0 i) 1) (elements a 0 n)); rewrite Union_comm.
   apply Union_assoc.
   generalize (Parent_inf i); unfold parent; intro; auto with zarith.
Qed.
(* DO NOT EDIT BELOW *)


