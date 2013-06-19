(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require list.List.
Require list.Length.
Require list.Mem.
Require map.Map.
Require list.Append.

(* Why3 assumption *)
Definition unit := unit.

(* Why3 assumption *)
Inductive distinct {a:Type} {a_WT:WhyType a} : (list a) -> Prop :=
  | distinct_zero : ((@distinct _ _) nil)
  | distinct_one : forall (x:a), ((@distinct _ _) (cons x nil))
  | distinct_many : forall (x:a) (l:(list a)), (~ (list.Mem.mem x l)) ->
      (((@distinct _ _) l) -> ((@distinct _ _) (cons x l))).

Axiom distinct_append : forall {a:Type} {a_WT:WhyType a},
  forall (l1:(list a)) (l2:(list a)), (distinct l1) -> ((distinct l2) ->
  ((forall (x:a), (list.Mem.mem x l1) -> ~ (list.Mem.mem x l2)) -> (distinct
  (List.app l1 l2)))).

(* Why3 assumption *)
Inductive array
  (a:Type) {a_WT:WhyType a} :=
  | mk_array : Z -> (@map.Map.map Z _ a a_WT) -> array a.
Axiom array_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.
Implicit Arguments mk_array [[a] [a_WT]].

(* Why3 assumption *)
Definition elts {a:Type} {a_WT:WhyType a} (v:(@array a a_WT)): (@map.Map.map
  Z _ a a_WT) := match v with
  | (mk_array x x1) => x1
  end.

(* Why3 assumption *)
Definition length {a:Type} {a_WT:WhyType a} (v:(@array a a_WT)): Z :=
  match v with
  | (mk_array x x1) => x
  end.

(* Why3 assumption *)
Definition get {a:Type} {a_WT:WhyType a} (a1:(@array a a_WT)) (i:Z): a :=
  (map.Map.get (elts a1) i).

(* Why3 assumption *)
Definition set {a:Type} {a_WT:WhyType a} (a1:(@array a a_WT)) (i:Z)
  (v:a): (@array a a_WT) := (mk_array (length a1) (map.Map.set (elts a1) i
  v)).

(* Why3 assumption *)
Definition make {a:Type} {a_WT:WhyType a} (n:Z) (v:a): (@array a a_WT) :=
  (mk_array n (map.Map.const v:(@map.Map.map Z _ a a_WT))).

(* Why3 assumption *)
Inductive tree :=
  | Empty : tree
  | Node : tree -> tree -> tree.
Axiom tree_WhyType : WhyType tree.
Existing Instance tree_WhyType.

(* Why3 assumption *)
Fixpoint size (t:tree) {struct t}: Z :=
  match t with
  | Empty => 0%Z
  | (Node l r) => ((1%Z + (size l))%Z + (size r))%Z
  end.

Axiom size_nonneg : forall (t:tree), (0%Z <= (size t))%Z.

Axiom size_left : forall (t:tree), (0%Z < (size t))%Z -> exists l:tree,
  exists r:tree, (t = (Node l r)) /\ ((size l) < (size t))%Z.

(* Why3 assumption *)
Definition all_trees (n:Z) (l:(list tree)): Prop := (distinct l) /\
  forall (t:tree), ((size t) = n) <-> (list.Mem.mem t l).

Axiom all_trees_0 : (all_trees 0%Z (cons Empty nil)).

Axiom tree_diff : forall (l1:tree) (l2:tree), (~ ((size l1) = (size l2))) ->
  forall (r1:tree) (r2:tree), ~ ((Node l1 r1) = (Node l2 r2)).

(* Why3 goal *)
Theorem WP_parameter_combine : forall (i1:Z) (l1:(list tree)) (i2:Z)
  (l2:(list tree)), ((0%Z <= i1)%Z /\ ((all_trees i1 l1) /\ ((0%Z <= i2)%Z /\
  (all_trees i2 l2)))) -> forall (l11:(list tree)), (distinct l11) ->
  match l11 with
  | nil => True
  | (cons t1 l12) => forall (l21:(list tree)), (distinct l21) ->
      match l21 with
      | nil => True
      | (cons t2 l22) => (distinct l22) -> forall (o:(list tree)), ((distinct
          o) /\ forall (t:tree), (list.Mem.mem t o) <-> exists r:tree,
          (t = (Node t1 r)) /\ (list.Mem.mem r l22)) -> forall (t:tree),
          (list.Mem.mem t (cons (Node t1 t2) o)) -> exists r:tree,
          (t = (Node t1 r)) /\ (list.Mem.mem r l21)
      end
  end.
(* Why3 intros i1 l1 i2 l2 (h1,(h2,(h3,h4))) l11 h5. *)
intuition.
destruct l11; intuition.
destruct l21; intuition.
unfold Mem.mem in H6; fold @Mem.mem in H6.
destruct H6.
exists t0; intuition.
red; intuition.
generalize (H8 t1). intuition.
destruct H9 as (r,h); exists r; intuition.
red; intuition.
Qed.


