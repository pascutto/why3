(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require int.Abs.
Require int.MinMax.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require int.Power.
Require map.Map.
Require map.Const.
Require bv.Pow2int.
Require bv.BV_Gen.
Require bool.Bool.

(* Why3 assumption *)
Definition unit := unit.

Axiom array : forall (a:Type), Type.
Parameter array_WhyType : forall (a:Type) {a_WT:WhyType a},
  WhyType (array a).
Existing Instance array_WhyType.

Parameter elts: forall {a:Type} {a_WT:WhyType a}, (array a) -> (Z -> a).

Parameter length: forall {a:Type} {a_WT:WhyType a}, (array a) -> Z.

Axiom inv_array : forall {a:Type} {a_WT:WhyType a}, forall (self:(array a)),
  (0%Z <= (length self))%Z.

(* Why3 assumption *)
Definition mixfix_lbrb {a:Type} {a_WT:WhyType a} (a1:(array a)) (i:Z): a :=
  ((elts a1) i).

Parameter mixfix_lblsmnrb: forall {a:Type} {a_WT:WhyType a}, (array a) ->
  Z -> a -> (array a).

Axiom mixfix_lblsmnrb_spec : forall {a:Type} {a_WT:WhyType a},
  forall (a1:(array a)) (i:Z) (v:a), ((length (mixfix_lblsmnrb a1 i
  v)) = (length a1)) /\ ((elts (mixfix_lblsmnrb a1 i
  v)) = (map.Map.set (elts a1) i v)).

Axiom int32 : Type.
Parameter int32_WhyType : WhyType int32.
Existing Instance int32_WhyType.

Parameter to_int: int32 -> Z.

(* Why3 assumption *)
Definition in_bounds (n:Z): Prop := ((-2147483648%Z)%Z <= n)%Z /\
  (n <= 2147483647%Z)%Z.

Axiom to_int_in_bounds : forall (n:int32), (in_bounds (to_int n)).

Axiom extensionality : forall (x:int32) (y:int32),
  ((to_int x) = (to_int y)) -> (x = y).

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter nth: t -> Z -> bool.

Axiom nth_out_of_bound : forall (x:t) (n:Z), ((n < 0%Z)%Z \/
  (32%Z <= n)%Z) -> ((nth x n) = false).

Parameter zeros: t.

Axiom Nth_zeros : forall (n:Z), ((nth zeros n) = false).

Parameter ones: t.

Axiom Nth_ones : forall (n:Z), ((0%Z <= n)%Z /\ (n < 32%Z)%Z) -> ((nth ones
  n) = true).

Parameter bw_and: t -> t -> t.

Axiom Nth_bw_and : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 32%Z)%Z) -> ((nth (bw_and v1 v2) n) = (Init.Datatypes.andb (nth v1
  n) (nth v2 n))).

Parameter bw_or: t -> t -> t.

Axiom Nth_bw_or : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 32%Z)%Z) -> ((nth (bw_or v1 v2) n) = (Init.Datatypes.orb (nth v1
  n) (nth v2 n))).

Parameter bw_xor: t -> t -> t.

Axiom Nth_bw_xor : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 32%Z)%Z) -> ((nth (bw_xor v1 v2) n) = (Init.Datatypes.xorb (nth v1
  n) (nth v2 n))).

Parameter bw_not: t -> t.

Axiom Nth_bw_not : forall (v:t) (n:Z), ((0%Z <= n)%Z /\ (n < 32%Z)%Z) ->
  ((nth (bw_not v) n) = (Init.Datatypes.negb (nth v n))).

Parameter lsr: t -> Z -> t.

Axiom Lsr_nth_low : forall (b:t) (n:Z) (s:Z), (0%Z <= s)%Z ->
  ((0%Z <= n)%Z -> (((n + s)%Z < 32%Z)%Z -> ((nth (lsr b s) n) = (nth b
  (n + s)%Z)))).

Axiom Lsr_nth_high : forall (b:t) (n:Z) (s:Z), (0%Z <= s)%Z ->
  ((0%Z <= n)%Z -> ((32%Z <= (n + s)%Z)%Z -> ((nth (lsr b s) n) = false))).

Axiom lsr_zeros : forall (x:t), ((lsr x 0%Z) = x).

Parameter asr: t -> Z -> t.

Axiom Asr_nth_low : forall (b:t) (n:Z) (s:Z), (0%Z <= s)%Z ->
  (((0%Z <= n)%Z /\ (n < 32%Z)%Z) -> (((n + s)%Z < 32%Z)%Z -> ((nth (asr b s)
  n) = (nth b (n + s)%Z)))).

Axiom Asr_nth_high : forall (b:t) (n:Z) (s:Z), (0%Z <= s)%Z ->
  (((0%Z <= n)%Z /\ (n < 32%Z)%Z) -> ((32%Z <= (n + s)%Z)%Z -> ((nth (asr b
  s) n) = (nth b (32%Z - 1%Z)%Z)))).

Axiom asr_zeros : forall (x:t), ((asr x 0%Z) = x).

Parameter lsl: t -> Z -> t.

Axiom Lsl_nth_high : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  ((s <= n)%Z /\ (n < 32%Z)%Z)) -> ((nth (lsl b s) n) = (nth b (n - s)%Z)).

Axiom Lsl_nth_low : forall (b:t) (n:Z) (s:Z), ((0%Z <= n)%Z /\ (n < s)%Z) ->
  ((nth (lsl b s) n) = false).

Axiom lsl_zeros : forall (x:t), ((lsl x 0%Z) = x).

Parameter rotate_right: t -> Z -> t.

Axiom Nth_rotate_right : forall (v:t) (n:Z) (i:Z), ((0%Z <= i)%Z /\
  (i < 32%Z)%Z) -> ((0%Z <= n)%Z -> ((nth (rotate_right v n) i) = (nth v
  (int.EuclideanDivision.mod1 (i + n)%Z 32%Z)))).

Parameter rotate_left: t -> Z -> t.

Axiom Nth_rotate_left : forall (v:t) (n:Z) (i:Z), ((0%Z <= i)%Z /\
  (i < 32%Z)%Z) -> ((0%Z <= n)%Z -> ((nth (rotate_left v n) i) = (nth v
  (int.EuclideanDivision.mod1 (i - n)%Z 32%Z)))).

Parameter to_int1: t -> Z.

Parameter to_uint: t -> Z.

Parameter of_int: Z -> t.

Axiom to_uint_extensionality : forall (v:t) (v':t),
  ((to_uint v) = (to_uint v')) -> (v = v').

Axiom to_int_extensionality : forall (v:t) (v':t),
  ((to_int1 v) = (to_int1 v')) -> (v = v').

(* Why3 assumption *)
Definition uint_in_range (i:Z): Prop := (0%Z <= i)%Z /\
  (i <= 4294967295%Z)%Z.

Axiom to_uint_bounds : forall (v:t), (0%Z <= (to_uint v))%Z /\
  ((to_uint v) < 4294967296%Z)%Z.

Axiom to_uint_of_int : forall (i:Z), ((0%Z <= i)%Z /\
  (i < 4294967296%Z)%Z) -> ((to_uint (of_int i)) = i).

Axiom Of_int_zeros : (zeros = (of_int 0%Z)).

Axiom Of_int_ones : (ones = (of_int 4294967295%Z)).

(* Why3 assumption *)
Definition ult (x:t) (y:t): Prop := ((to_uint x) < (to_uint y))%Z.

(* Why3 assumption *)
Definition ule (x:t) (y:t): Prop := ((to_uint x) <= (to_uint y))%Z.

(* Why3 assumption *)
Definition ugt (x:t) (y:t): Prop := ((to_uint y) < (to_uint x))%Z.

(* Why3 assumption *)
Definition uge (x:t) (y:t): Prop := ((to_uint y) <= (to_uint x))%Z.

(* Why3 assumption *)
Definition slt (v1:t) (v2:t): Prop := ((to_int1 v1) < (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sle (v1:t) (v2:t): Prop := ((to_int1 v1) <= (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sgt (v1:t) (v2:t): Prop := ((to_int1 v2) < (to_int1 v1))%Z.

(* Why3 assumption *)
Definition sge (v1:t) (v2:t): Prop := ((to_int1 v2) <= (to_int1 v1))%Z.

Parameter add: t -> t -> t.

Axiom to_uint_add : forall (v1:t) (v2:t), ((to_uint (add v1
  v2)) = (int.EuclideanDivision.mod1 ((to_uint v1) + (to_uint v2))%Z
  4294967296%Z)).

Axiom to_uint_add_bounded : forall (v1:t) (v2:t),
  (((to_uint v1) + (to_uint v2))%Z < 4294967296%Z)%Z -> ((to_uint (add v1
  v2)) = ((to_uint v1) + (to_uint v2))%Z).

Parameter sub: t -> t -> t.

Axiom to_uint_sub : forall (v1:t) (v2:t), ((to_uint (sub v1
  v2)) = (int.EuclideanDivision.mod1 ((to_uint v1) - (to_uint v2))%Z
  4294967296%Z)).

Axiom to_uint_sub_bounded : forall (v1:t) (v2:t),
  ((0%Z <= ((to_uint v1) - (to_uint v2))%Z)%Z /\
  (((to_uint v1) - (to_uint v2))%Z < 4294967296%Z)%Z) -> ((to_uint (sub v1
  v2)) = ((to_uint v1) - (to_uint v2))%Z).

Parameter neg: t -> t.

Axiom to_uint_neg : forall (v:t),
  ((to_uint (neg v)) = (int.EuclideanDivision.mod1 (-(to_uint v))%Z
  4294967296%Z)).

Parameter mul: t -> t -> t.

Axiom to_uint_mul : forall (v1:t) (v2:t), ((to_uint (mul v1
  v2)) = (int.EuclideanDivision.mod1 ((to_uint v1) * (to_uint v2))%Z
  4294967296%Z)).

Axiom to_uint_mul_bounded : forall (v1:t) (v2:t),
  (((to_uint v1) * (to_uint v2))%Z < 4294967296%Z)%Z -> ((to_uint (mul v1
  v2)) = ((to_uint v1) * (to_uint v2))%Z).

Parameter udiv: t -> t -> t.

Axiom to_uint_udiv : forall (v1:t) (v2:t), ((to_uint (udiv v1
  v2)) = (int.EuclideanDivision.div (to_uint v1) (to_uint v2))).

Parameter urem: t -> t -> t.

Axiom to_uint_urem : forall (v1:t) (v2:t), ((to_uint (urem v1
  v2)) = (int.EuclideanDivision.mod1 (to_uint v1) (to_uint v2))).

Parameter lsr_bv: t -> t -> t.

Axiom lsr_bv_is_lsr : forall (x:t) (n:t), ((lsr_bv x n) = (lsr x
  (to_uint n))).

Axiom to_uint_lsr : forall (v:t) (n:t), ((to_uint (lsr_bv v
  n)) = (int.EuclideanDivision.div (to_uint v)
  (bv.Pow2int.pow2 (to_uint n)))).

Parameter asr_bv: t -> t -> t.

Axiom asr_bv_is_asr : forall (x:t) (n:t), ((asr_bv x n) = (asr x
  (to_uint n))).

Parameter lsl_bv: t -> t -> t.

Axiom lsl_bv_is_lsl : forall (x:t) (n:t), ((lsl_bv x n) = (lsl x
  (to_uint n))).

Axiom to_uint_lsl : forall (v:t) (n:t), ((to_uint (lsl_bv v
  n)) = (int.EuclideanDivision.mod1 ((to_uint v) * (bv.Pow2int.pow2 (to_uint n)))%Z
  4294967296%Z)).

Parameter rotate_right_bv: t -> t -> t.

Parameter rotate_left_bv: t -> t -> t.

Axiom rotate_left_bv_is_rotate_left : forall (v:t) (n:t), ((rotate_left_bv v
  n) = (rotate_left v (to_uint n))).

Axiom rotate_right_bv_is_rotate_right : forall (v:t) (n:t),
  ((rotate_right_bv v n) = (rotate_right v (to_uint n))).

Parameter nth_bv: t -> t -> bool.

Axiom nth_bv_def : forall (x:t) (i:t), ((nth_bv x i) = true) <->
  ~ ((bw_and (lsr_bv x i) (of_int 1%Z)) = zeros).

Axiom Nth_bv_is_nth : forall (x:t) (i:t), ((nth x (to_uint i)) = (nth_bv x
  i)).

Axiom Nth_bv_is_nth2 : forall (x:t) (i:Z), ((0%Z <= i)%Z /\
  (i < 4294967296%Z)%Z) -> ((nth_bv x (of_int i)) = (nth x i)).

Parameter eq_sub_bv: t -> t -> t -> t -> Prop.

Axiom eq_sub_bv_def : forall (a:t) (b:t) (i:t) (n:t), let mask :=
  (lsl_bv (sub (lsl_bv (of_int 1%Z) n) (of_int 1%Z)) i) in ((eq_sub_bv a b i
  n) <-> ((bw_and b mask) = (bw_and a mask))).

(* Why3 assumption *)
Definition eq_sub (a:t) (b:t) (i:Z) (n:Z): Prop := forall (j:Z),
  ((i <= j)%Z /\ (j < (i + n)%Z)%Z) -> ((nth a j) = (nth b j)).

Axiom eq_sub_equiv : forall (a:t) (b:t) (i:t) (n:t), (eq_sub a b (to_uint i)
  (to_uint n)) <-> (eq_sub_bv a b i n).

Axiom Extensionality : forall (x:t) (y:t), (eq_sub x y 0%Z 32%Z) -> (x = y).

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Implicit Arguments mk_ref [[a]].

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.

(* Why3 assumption *)
Definition map_eq_sub {a:Type} {a_WT:WhyType a} (a1:(Z -> a)) (a2:(Z -> a))
  (l:Z) (u:Z): Prop := forall (i:Z), ((l <= i)%Z /\ (i < u)%Z) -> ((a1
  i) = (a2 i)).

(* Why3 assumption *)
Definition map_eq_sub_shift {a:Type} {a_WT:WhyType a} (x:(Z -> a)) (y:(Z ->
  a)) (xi:Z) (yi:Z) (sz:Z): Prop := forall (i:Z), ((0%Z <= i)%Z /\
  (i < sz)%Z) -> ((x (xi + i)%Z) = (y (yi + i)%Z)).

Axiom map_eq_shift : forall {a:Type} {a_WT:WhyType a}, forall (x:(Z -> a))
  (y:(Z -> a)) (xi:Z) (yi:Z) (sz:Z) (k:Z), (map_eq_sub_shift x y xi yi sz) ->
  (((0%Z <= k)%Z /\ (k < sz)%Z) -> ((x (xi + k)%Z) = (y (yi + k)%Z))).

Axiom map_eq_shift_zero : forall {a:Type} {a_WT:WhyType a}, forall (x:(Z ->
  a)) (y:(Z -> a)) (n:Z) (m:Z), (map_eq_sub_shift x y n n (m - n)%Z) ->
  (map_eq_sub x y n m).

Axiom uint64 : Type.
Parameter uint64_WhyType : WhyType uint64.
Existing Instance uint64_WhyType.

Parameter to_int2: uint64 -> Z.

(* Why3 assumption *)
Definition in_bounds1 (n:Z): Prop := (0%Z <= n)%Z /\
  (n <= 18446744073709551615%Z)%Z.

Axiom to_int_in_bounds1 : forall (n:uint64), (in_bounds1 (to_int2 n)).

Axiom extensionality1 : forall (x:uint64) (y:uint64),
  ((to_int2 x) = (to_int2 y)) -> (x = y).

Parameter zero_unsigned: uint64.

Axiom zero_unsigned_is_zero : ((to_int2 zero_unsigned) = 0%Z).

Parameter is_msb_set: uint64 -> Prop.

Axiom is_msb_set_spec : forall (x:uint64), (is_msb_set x) <->
  (18446744073709551615%Z < (2%Z * (to_int2 x))%Z)%Z.

(* Why3 assumption *)
Definition limb := uint64.

Axiom limb_max_bound : (1%Z <= 18446744073709551615%Z)%Z.

Axiom prod_compat_strict_r : forall (a:Z) (b:Z) (c:Z), ((0%Z <= a)%Z /\
  (a < b)%Z) -> ((0%Z < c)%Z -> ((c * a)%Z < (c * b)%Z)%Z).

Parameter value_sub: (Z -> uint64) -> Z -> Z -> Z.

Axiom value_sub_def : forall (x:(Z -> uint64)) (n:Z) (m:Z), ((n < m)%Z ->
  ((value_sub x n m) = ((to_int2 (x
  n)) + ((18446744073709551615%Z + 1%Z)%Z * (value_sub x (n + 1%Z)%Z
  m))%Z)%Z)) /\ ((~ (n < m)%Z) -> ((value_sub x n m) = 0%Z)).

Axiom value_sub_frame : forall (x:(Z -> uint64)) (y:(Z -> uint64)) (n:Z)
  (m:Z), (map_eq_sub x y n m) -> ((value_sub x n m) = (value_sub y n m)).

Axiom value_sub_frame_shift : forall (x:(Z -> uint64)) (y:(Z -> uint64))
  (xi:Z) (yi:Z) (sz:Z), (map_eq_sub_shift x y xi yi sz) -> ((value_sub x xi
  (xi + sz)%Z) = (value_sub y yi (yi + sz)%Z)).

Axiom value_sub_tail : forall (x:(Z -> uint64)) (n:Z) (m:Z), (n <= m)%Z ->
  ((value_sub x n (m + 1%Z)%Z) = ((value_sub x n m) + ((to_int2 (x
  m)) * (int.Power.power (18446744073709551615%Z + 1%Z)%Z (m - n)%Z))%Z)%Z).

Axiom value_sub_concat : forall (x:(Z -> uint64)) (n:Z) (m:Z) (l:Z),
  ((n <= m)%Z /\ (m <= l)%Z) -> ((value_sub x n l) = ((value_sub x n
  m) + ((value_sub x m l) * (int.Power.power (18446744073709551615%Z + 1%Z)%Z
  (m - n)%Z))%Z)%Z).

Axiom value_sub_head : forall (x:(Z -> uint64)) (n:Z) (m:Z), (n < m)%Z ->
  ((value_sub x n m) = ((to_int2 (x
  n)) + ((18446744073709551615%Z + 1%Z)%Z * (value_sub x (n + 1%Z)%Z
  m))%Z)%Z).

Axiom value_sub_update : forall (x:(Z -> uint64)) (i:Z) (n:Z) (m:Z)
  (v:uint64), ((n <= i)%Z /\ (i < m)%Z) -> ((value_sub (map.Map.set x i v) n
  m) = ((value_sub x n
  m) + ((int.Power.power (18446744073709551615%Z + 1%Z)%Z
  (i - n)%Z) * ((to_int2 v) - (to_int2 (x i)))%Z)%Z)%Z).

Axiom value_zero : forall (x:(Z -> uint64)) (n:Z) (m:Z), (map_eq_sub x
  (map.Const.const zero_unsigned: (Z -> uint64)) n m) -> ((value_sub x n
  m) = 0%Z).

Axiom value_sub_update_no_change : forall (x:(Z -> uint64)) (i:Z) (n:Z) (m:Z)
  (v:uint64), (n <= m)%Z -> (((i < n)%Z \/ (m <= i)%Z) -> ((value_sub x n
  m) = (value_sub (map.Map.set x i v) n m))).

Axiom value_sub_shift_no_change : forall (x:(Z -> uint64)) (ofs:Z) (i:Z)
  (sz:Z) (v:uint64), ((i < 0%Z)%Z \/ (sz <= i)%Z) -> ((0%Z <= sz)%Z ->
  ((value_sub x ofs (ofs + sz)%Z) = (value_sub (map.Map.set x (ofs + i)%Z v)
  ofs (ofs + sz)%Z))).

Axiom value_sub_lower_bound : forall (x:(Z -> uint64)) (x1:Z) (x2:Z),
  (0%Z <= (value_sub x x1 x2))%Z.

Axiom value_sub_upper_bound : forall (x:(Z -> uint64)) (x1:Z) (x2:Z),
  (x1 <= x2)%Z -> ((value_sub x x1
  x2) < (int.Power.power (18446744073709551615%Z + 1%Z)%Z (x2 - x1)%Z))%Z.

Axiom value_sub_lower_bound_tight : forall (x:(Z -> uint64)) (x1:Z) (x2:Z),
  (x1 < x2)%Z -> (((int.Power.power (18446744073709551615%Z + 1%Z)%Z
  ((x2 - x1)%Z - 1%Z)%Z) * (to_int2 (x (x2 - 1%Z)%Z)))%Z <= (value_sub x x1
  x2))%Z.

Axiom value_sub_upper_bound_tight : forall (x:(Z -> uint64)) (x1:Z) (x2:Z),
  (x1 < x2)%Z -> ((value_sub x x1
  x2) < ((int.Power.power (18446744073709551615%Z + 1%Z)%Z
  ((x2 - x1)%Z - 1%Z)%Z) * ((to_int2 (x (x2 - 1%Z)%Z)) + 1%Z)%Z)%Z)%Z.

Axiom t1 : Type.
Parameter t1_WhyType : WhyType t1.
Existing Instance t1_WhyType.

Parameter max: Z.

Parameter to_int3: t1 -> Z.

(* Why3 assumption *)
Definition in_bounds2 (n:Z): Prop := (0%Z <= n)%Z /\ (n <= max)%Z.

Axiom to_int_in_bounds2 : forall (n:t1), (in_bounds2 (to_int3 n)).

Axiom extensionality2 : forall (x:t1) (y:t1), ((to_int3 x) = (to_int3 y)) ->
  (x = y).

Parameter zero_unsigned1: t1.

Axiom zero_unsigned_is_zero1 : ((to_int3 zero_unsigned1) = 0%Z).

Axiom uint32 : Type.
Parameter uint32_WhyType : WhyType uint32.
Existing Instance uint32_WhyType.

Parameter to_int4: uint32 -> Z.

(* Why3 assumption *)
Definition in_bounds3 (n:Z): Prop := (0%Z <= n)%Z /\ (n <= 4294967295%Z)%Z.

Axiom to_int_in_bounds3 : forall (n:uint32), (in_bounds3 (to_int4 n)).

Axiom extensionality3 : forall (x:uint32) (y:uint32),
  ((to_int4 x) = (to_int4 y)) -> (x = y).

Parameter zero_unsigned2: uint32.

Axiom zero_unsigned_is_zero2 : ((to_int4 zero_unsigned2) = 0%Z).

Parameter is_msb_set1: uint32 -> Prop.

Axiom is_msb_set_spec1 : forall (x:uint32), (is_msb_set1 x) <->
  (4294967295%Z < (2%Z * (to_int4 x))%Z)%Z.

(* Why3 assumption *)
Definition in_us_bounds (n:Z): Prop := (0%Z <= n)%Z /\ (n <= 4294967295%Z)%Z.

(* Why3 assumption *)
Definition in_bounds4 (n:Z): Prop := ((-2147483648%Z)%Z <= n)%Z /\
  (n <= 2147483647%Z)%Z.

(* Why3 assumption *)
Inductive ptr (a:Type) :=
  | mk_ptr : (ref (array a)) -> Z -> ptr a.
Axiom ptr_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ptr a).
Existing Instance ptr_WhyType.
Implicit Arguments mk_ptr [[a]].

(* Why3 assumption *)
Definition offset {a:Type} {a_WT:WhyType a} (v:(ptr a)): Z :=
  match v with
  | (mk_ptr x x1) => x1
  end.

(* Why3 assumption *)
Definition data {a:Type} {a_WT:WhyType a} (v:(ptr a)): (ref (array a)) :=
  match v with
  | (mk_ptr x x1) => x
  end.

(* Why3 assumption *)
Definition plength {a:Type} {a_WT:WhyType a} (p:(ptr a)): Z :=
  (length (contents (data p))).

(* Why3 assumption *)
Definition pelts {a:Type} {a_WT:WhyType a} (p:(ptr a)): (Z -> a) :=
  (elts (contents (data p))).

Parameter is_null: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> Prop.

Axiom is_null_spec : forall {a:Type} {a_WT:WhyType a}, forall (p:(ptr a)),
  (is_null p) <-> ((plength p) = 0%Z).

(* Why3 assumption *)
Definition valid_ptr_shift {a:Type} {a_WT:WhyType a} (p:(ptr a))
  (i:Z): Prop := (0%Z <= ((offset p) + i)%Z)%Z /\
  (((offset p) + i)%Z < (plength p))%Z.

(* Why3 assumption *)
Definition valid_ptr_itv {a:Type} {a_WT:WhyType a} (p:(ptr a))
  (sz:Z): Prop := (in_bounds4 sz) /\ ((0%Z <= sz)%Z /\
  ((0%Z <= (offset p))%Z /\ (((offset p) + sz)%Z <= (plength p))%Z)).

Axiom valid_itv_to_shift : forall {a:Type} {a_WT:WhyType a}, forall (p:(ptr
  a)) (sz:Z), (valid_ptr_itv p sz) -> forall (i:Z), ((0%Z <= i)%Z /\
  (i < sz)%Z) -> (valid_ptr_shift p i).

(* Why3 assumption *)
Definition t2 := (ptr uint64).

(* Why3 assumption *)
Definition value (x:(ptr uint64)): Z := (value_sub (pelts x) 0%Z
  (plength x)).

(* Why3 assumption *)
Definition value_sub_shift (x:(ptr uint64)) (sz:Z): Z := (value_sub (pelts x)
  (offset x) ((offset x) + sz)%Z).

Parameter compare_int: Z -> Z -> Z.

Axiom compare_int_def : forall (x:Z) (y:Z), ((x < y)%Z -> ((compare_int x
  y) = (-1%Z)%Z)) /\ ((~ (x < y)%Z) -> (((x = y) -> ((compare_int x
  y) = 0%Z)) /\ ((~ (x = y)) -> ((compare_int x y) = 1%Z)))).

Axiom pow2_64 : ((int.Power.power 2%Z
  64%Z) = (18446744073709551615%Z + 1%Z)%Z).

Axiom mod_mult : forall (x:Z) (y:Z) (z:Z), (0%Z < x)%Z ->
  ((int.EuclideanDivision.mod1 ((x * y)%Z + z)%Z
  x) = (int.EuclideanDivision.mod1 z x)).

(* Why3 assumption *)
Definition reciprocal (v:uint64) (d:uint64): Prop :=
  ((to_int2 v) = ((int.EuclideanDivision.div (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - 1%Z)%Z
  (to_int2 d)) - (18446744073709551615%Z + 1%Z)%Z)%Z).

Axiom fact_div : forall (x:Z) (y:Z) (z:Z), (0%Z < y)%Z ->
  ((int.EuclideanDivision.div (x + (y * z)%Z)%Z
  y) = ((int.EuclideanDivision.div x y) + z)%Z).

(* Why3 assumption *)
Definition reciprocal_3by2 (v:uint64) (dh:uint64) (dl:uint64): Prop :=
  ((to_int2 v) = ((int.EuclideanDivision.div ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - 1%Z)%Z
  ((to_int2 dl) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z) - (18446744073709551615%Z + 1%Z)%Z)%Z).

(* Why3 goal *)
Theorem VC_div3by2_inv : forall (uh:uint64) (um:uint64) (ul:uint64)
  (dh:uint64) (dl:uint64) (v:uint64),
  (((int.EuclideanDivision.div (18446744073709551615%Z + 1%Z)%Z
  2%Z) <= (to_int2 dh))%Z /\ ((reciprocal_3by2 v dh dl) /\
  (((to_int2 um) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 uh))%Z)%Z < ((to_int2 dl) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z)%Z)) ->
  let d :=
  ((to_int2 dl) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z in
  forall (zero:uint64), ((to_int2 zero) = 0%Z) -> forall (one:uint64),
  ((to_int2 one) = 1%Z) -> forall (o:uint64) (o1:uint64),
  (((to_int2 o) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o1))%Z)%Z = ((to_int2 v) * (to_int2 uh))%Z) ->
  forall (o2:uint64) (o3:uint64),
  ((((to_int2 o2) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o3))%Z)%Z = (((to_int2 um) + (to_int2 o))%Z + (to_int2 zero))%Z) /\
  ((0%Z <= (to_int2 o3))%Z /\ ((to_int2 o3) <= 1%Z)%Z)) -> forall (o4:uint64)
  (o5:uint64),
  ((((to_int2 o4) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o5))%Z)%Z = (((to_int2 uh) + (to_int2 o1))%Z + (to_int2 o3))%Z) /\
  ((0%Z <= (to_int2 o5))%Z /\ ((to_int2 o5) <= 1%Z)%Z)) ->
  (((((to_int2 o2) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o4))%Z)%Z + (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (to_int2 o5))%Z)%Z = (((to_int2 um) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 uh))%Z)%Z + ((to_int2 v) * (to_int2 uh))%Z)%Z) ->
  (((to_int2 o5) = 0%Z) -> forall (q1:uint64), (q1 = o4) -> let q0 :=
  (to_int2 o2) in let cq := ((to_int2 q1) + 1%Z)%Z in forall (o6:uint64),
  ((to_int2 o6) = (int.EuclideanDivision.mod1 ((to_int2 q1) + (to_int2 one))%Z
  (18446744073709551615%Z + 1%Z)%Z)) -> forall (q11:uint64), (q11 = o6) ->
  (((to_int2 q11) = (int.EuclideanDivision.mod1 cq
  (18446744073709551615%Z + 1%Z)%Z)) -> forall (p:uint64),
  ((to_int2 p) = (int.EuclideanDivision.mod1 ((to_int2 dh) * (to_int2 o4))%Z
  (18446744073709551615%Z + 1%Z)%Z)) -> forall (o7:uint64),
  ((to_int2 o7) = (int.EuclideanDivision.mod1 ((to_int2 um) - (to_int2 p))%Z
  (18446744073709551615%Z + 1%Z)%Z)) -> forall (r1:uint64), (r1 = o7) ->
  forall (o8:uint64) (o9:uint64),
  (((to_int2 o8) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o9))%Z)%Z = ((to_int2 o4) * (to_int2 dl))%Z) ->
  forall (o10:uint64) (o11:uint64),
  ((((to_int2 o10) - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o11))%Z)%Z = (((to_int2 ul) - (to_int2 o8))%Z - (to_int2 zero))%Z) /\
  ((0%Z <= (to_int2 o11))%Z /\ ((to_int2 o11) <= 1%Z)%Z)) ->
  forall (o12:uint64) (o13:uint64),
  ((((to_int2 o12) - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o13))%Z)%Z = (((to_int2 r1) - (to_int2 o9))%Z - (to_int2 o11))%Z) /\
  ((0%Z <= (to_int2 o13))%Z /\ ((to_int2 o13) <= 1%Z)%Z)) ->
  (((((to_int2 o10) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o12))%Z)%Z - (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (to_int2 o13))%Z)%Z = (((to_int2 ul) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 r1))%Z)%Z - ((to_int2 o4) * (to_int2 dl))%Z)%Z) ->
  forall (o14:uint64) (o15:uint64),
  ((((to_int2 o14) - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o15))%Z)%Z = (((to_int2 o10) - (to_int2 dl))%Z - (to_int2 zero))%Z) /\
  ((0%Z <= (to_int2 o15))%Z /\ ((to_int2 o15) <= 1%Z)%Z)) ->
  forall (o16:uint64) (o17:uint64),
  ((((to_int2 o16) - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o17))%Z)%Z = (((to_int2 o12) - (to_int2 dh))%Z - (to_int2 o15))%Z) /\
  ((0%Z <= (to_int2 o17))%Z /\ ((to_int2 o17) <= 1%Z)%Z)) ->
  (((((to_int2 o14) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o16))%Z)%Z - (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (to_int2 o17))%Z)%Z = ((((to_int2 o10) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o12))%Z)%Z - (to_int2 dl))%Z - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z) ->
  let o18 :=
  (((((to_int2 ul) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 r1))%Z)%Z - ((to_int2 o4) * (to_int2 dl))%Z)%Z - (to_int2 dl))%Z - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z in
  let o19 :=
  ((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z in
  (((int.EuclideanDivision.mod1 ((o19 * (to_int2 o13))%Z + o18)%Z
  o19) = (int.EuclideanDivision.mod1 o18 o19)) ->
  ((((to_int2 o14) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o16))%Z)%Z = (int.EuclideanDivision.mod1 (((((to_int2 ul) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 r1))%Z)%Z - ((to_int2 o4) * (to_int2 dl))%Z)%Z - (to_int2 dl))%Z - ((18446744073709551615%Z + 1%Z)%Z * (to_int2 dh))%Z)%Z
  ((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z)) ->
  forall (r11:uint64), (r11 = o16) -> forall (r0:uint64), (r0 = o14) ->
  let cr :=
  (((to_int2 ul) + ((18446744073709551615%Z + 1%Z)%Z * ((to_int2 um) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 uh))%Z)%Z)%Z)%Z - (d * cq)%Z)%Z in
  ((((to_int2 r0) + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 r11))%Z)%Z = (int.EuclideanDivision.mod1 cr
  ((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z)) ->
  let k :=
  ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - (((18446744073709551615%Z + 1%Z)%Z + (to_int2 v))%Z * d)%Z)%Z in
  ((reciprocal_3by2 v dh dl) -> let m3 :=
  ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - 1%Z)%Z in
  ((((((18446744073709551615%Z + 1%Z)%Z + (to_int2 v))%Z * d)%Z = (d * (int.EuclideanDivision.div m3
  d))%Z) /\ ((d * (int.EuclideanDivision.div m3
  d))%Z = (m3 - (int.EuclideanDivision.mod1 m3 d))%Z)) ->
  ((k = (1%Z + (int.EuclideanDivision.mod1 m3 d))%Z) -> (((1%Z <= k)%Z /\
  (k <= d)%Z) ->
  (((q0 + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 o4))%Z)%Z = ((((18446744073709551615%Z + 1%Z)%Z + (to_int2 v))%Z * (to_int2 uh))%Z + (to_int2 um))%Z) ->
  ((cq = ((to_int2 o4) + 1%Z)%Z) ->
  (((((18446744073709551615%Z + 1%Z)%Z * cq)%Z = (((18446744073709551615%Z + 1%Z)%Z * (to_int2 o4))%Z + (18446744073709551615%Z + 1%Z)%Z)%Z) /\
  ((((18446744073709551615%Z + 1%Z)%Z * (to_int2 o4))%Z + (18446744073709551615%Z + 1%Z)%Z)%Z = ((((((18446744073709551615%Z + 1%Z)%Z + (to_int2 v))%Z * (to_int2 uh))%Z + (to_int2 um))%Z - q0)%Z + (18446744073709551615%Z + 1%Z)%Z)%Z)) ->
  ((((18446744073709551615%Z + 1%Z)%Z * cr)%Z = (((((k * (to_int2 uh))%Z + ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - d)%Z * (to_int2 um))%Z)%Z + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 ul))%Z)%Z + (d * q0)%Z)%Z - (d * (18446744073709551615%Z + 1%Z)%Z)%Z)%Z) ->
  ((((ZArith.BinInt.Z.max (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - d)%Z (q0 * (18446744073709551615%Z + 1%Z)%Z)%Z) - ((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z)%Z <= cr)%Z ->
  ((0%Z < (((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - d)%Z)%Z ->
  ((~ ((to_int2 uh) <= ((to_int2 dh) - 1%Z)%Z)%Z) ->
  (((to_int2 uh) = (to_int2 dh)) ->
  (((to_int2 um) <= ((to_int2 dl) - 1%Z)%Z)%Z ->
  ((((((k * (to_int2 dh))%Z + ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - d)%Z * (to_int2 um))%Z)%Z + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 ul))%Z)%Z + (d * q0)%Z)%Z - ((18446744073709551615%Z + 1%Z)%Z * d)%Z)%Z <= (((((d * (to_int2 dh))%Z + ((((18446744073709551615%Z + 1%Z)%Z * (18446744073709551615%Z + 1%Z)%Z)%Z - d)%Z * (to_int2 um))%Z)%Z + ((18446744073709551615%Z + 1%Z)%Z * (to_int2 ul))%Z)%Z + (d * q0)%Z)%Z - ((18446744073709551615%Z + 1%Z)%Z * d)%Z)%Z)%Z))))))))))))))))))))).
(* Why3 intros uh um ul dh dl v (h1,(h2,h3)) d zero h4 one h5 o o1 h6 o2 o3
        (h7,(h8,h9)) o4 o5 (h10,(h11,h12)) h13 h14 q1 h15 q0 cq o6 h16 q11
        h17 h18 p h19 o7 h20 r1 h21 o8 o9 h22 o10 o11 (h23,(h24,h25)) o12 o13
        (h26,(h27,h28)) h29 o14 o15 (h30,(h31,h32)) o16 o17 (h33,(h34,h35))
        h36 o18 o19 h37 h38 r11 h39 r0 h40 cr h41 k h42 m3 (h43,h44) h45
        (h46,h47) h48 h49 (h50,h51) h52 h53 h54 h55 h56 h57. *)
intros uh um ul dh dl v (h1,(h2,h3)) d zero h4 one h5 o o1 h6 o2 o3
(h7,(h8,h9)) o4 o5 (h10,(h11,h12)) h13 h14 q1 h15 q0 cq o6 h16 q11 h17 h18 p
h19 o7 h20 r1 h21 o8 o9 h22 o10 o11 (h23,(h24,h25)) o12 o13 (h26,(h27,h28))
h29 o14 o15 (h30,(h31,h32)) o16 o17 (h33,(h34,h35)) h36 o18 o19 h37 h38 r11
h39 r0 h40 cr h41 k h42 m3 (h43,h44) h45 (h46,h47) h48 h49 (h50,h51) h52 h53
h54 h55 h56 h57.
apply Zplus_le_compat_r.
apply Zplus_le_compat_r.
apply Zplus_le_compat_r.
apply Zplus_le_compat_r.
apply Zmult_le_compat_r.
omega.
apply to_int_in_bounds1.
Qed.

