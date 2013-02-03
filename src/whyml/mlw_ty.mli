(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term

(** individual types (first-order types w/o effects) *)

module rec T : sig

  type varset = private {
    vars_tv  : Stv.t;
    vars_reg : Sreg.t;
  }

  type varmap = varset Mid.t

  type itysymbol = private {
    its_ts   : tysymbol;
    its_regs : region list;
    its_def  : ity option;
    its_inv  : bool;
    its_abst : bool;
    its_priv : bool;
  }

  (** ity = individual type in programs, first-order, i.e. no functions *)
  and ity = private {
    ity_node : ity_node;
    ity_vars : varset;
    ity_tag  : Weakhtbl.tag;
  }

  and ity_node = private
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = private {
    reg_name : ident;
    reg_ity  : ity;
  }

end
and Mreg : sig include Extmap.S with type key = T.region end
and Sreg : sig include Extset.S with module M = Mreg end

open T

module Mits : Extmap.S with type key = itysymbol
module Sits : Extset.S with module M = Mits
module Hits : Exthtbl.S with type key = itysymbol
module Wits : Weakhtbl.S with type key = itysymbol

module Mity : Extmap.S with type key = ity
module Sity : Extset.S with module M = Mity
module Hity : Exthtbl.S with type key = ity
module Wity : Weakhtbl.S with type key = ity

module Hreg : Exthtbl.S with type key = region
module Wreg : Weakhtbl.S with type key = region

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int

val reg_equal : region -> region -> bool
val reg_hash : region -> int

exception BadItyArity of itysymbol * int * int
exception BadRegArity of itysymbol * int * int
exception DuplicateRegion of region
exception UnboundRegion of region

val create_region : preid -> ity -> region


(** creation of a symbol for type in programs *)
val create_itysymbol :
  preid -> ?abst:bool -> ?priv:bool -> ?inv:bool ->
    tvsymbol list -> region list -> ity option -> itysymbol

val restore_its : tysymbol -> itysymbol
  (* raises Not_found if the argument is not a its_ts *)

val ity_var : tvsymbol -> ity
val ity_pur : tysymbol -> ity list -> ity

val ity_app : itysymbol -> ity list -> region list -> ity
val ity_app_fresh : itysymbol -> ity list -> ity

(* all aliases expanded, all regions removed *)
val ty_of_ity : ity -> ty

(* replaces every [Tyapp] with [Itypur] *)
val ity_of_ty : ty -> ity

(* generic traversal functions *)

val ity_map : (ity -> ity) -> ity -> ity
val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val ity_all : (ity -> bool) -> ity -> bool
val ity_any : (ity -> bool) -> ity -> bool

(* traversal functions on type symbols *)

val ity_s_fold :
  ('a -> itysymbol -> 'a) -> ('a -> tysymbol -> 'a) -> 'a -> ity -> 'a

val ity_s_all : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool
val ity_s_any : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool

val its_clone : Theory.symbol_map -> itysymbol Mits.t * region Mreg.t

val ity_closed    : ity -> bool
val ity_immutable : ity -> bool
val ity_has_inv   : ity -> bool

(* these functions attend the sub-regions *)

val reg_fold : (region -> 'a -> 'a) -> varset -> 'a -> 'a
val reg_any  : (region -> bool) -> varset -> bool
val reg_all  : (region -> bool) -> varset -> bool
val reg_iter : (region -> unit) -> varset -> unit

val reg_occurs : region -> varset -> bool

(* built-in types *)

val ts_unit : tysymbol (* the same as [Ty.ts_tuple 0] *)
val ty_unit : ty

val ity_int : ity
val ity_bool : ity
val ity_unit : ity

type ity_subst = private {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t;
}

exception RegionMismatch of region * region * ity_subst
exception TypeMismatch of ity * ity * ity_subst

val ity_subst_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst

val reg_match : ity_subst -> region -> region -> ity_subst

val ity_equal_check : ity -> ity -> unit

val reg_equal_check : region -> region -> unit

val ity_full_inst : ity_subst -> ity -> ity

val reg_full_inst : ity_subst -> region -> region

val vars_empty : varset

val vars_union : varset -> varset -> varset

val vars_merge : varmap -> varset -> varset

val vars_freeze : varset -> ity_subst

val create_varset : Stv.t -> Sreg.t -> varset

(* exception symbols *)
type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (* closed and immutable *)
}

val xs_equal : xsymbol -> xsymbol -> bool

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

val create_xsymbol : preid -> ity -> xsymbol

module Mexn: Extmap.S with type key = xsymbol
module Sexn: Extset.S with module M = Mexn

(** effects *)

type effect = private {
  eff_reads  : Sreg.t;
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostr : Sreg.t; (* ghost reads *)
  eff_ghostw : Sreg.t; (* ghost writes *)
  eff_ghostx : Sexn.t; (* ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
}

val eff_empty : effect
val eff_union : effect -> effect -> effect
val eff_ghostify : effect -> effect

val eff_read  : effect -> ?ghost:bool -> region -> effect
val eff_write : effect -> ?ghost:bool -> region -> effect
val eff_raise : effect -> ?ghost:bool -> xsymbol -> effect
val eff_reset : effect -> region -> effect

val eff_refresh : effect -> region -> region -> effect
val eff_assign : effect -> ?ghost:bool -> region -> ity -> effect

val eff_remove_raise : effect -> xsymbol -> effect

val eff_stale_region : effect -> varset -> bool

exception IllegalAlias of region

val eff_full_inst : ity_subst -> effect -> effect

val eff_filter : varset -> effect -> effect

val eff_is_empty : effect -> bool

(** specification *)

type pre = term          (* precondition: pre_fmla *)
type post = term         (* postcondition: eps result . post_fmla *)
type xpost = post Mexn.t (* exceptional postconditions *)

type variant = term * lsymbol option (* tau * (tau -> tau -> prop) *)

val create_post : vsymbol -> term -> post
val open_post : post -> vsymbol * term
val check_post : ty -> post -> unit

type spec = {
  c_pre     : pre;
  c_post    : post;
  c_xpost   : xpost;
  c_effect  : effect;
  c_variant : variant list;
  c_letrec  : int;
}

(** program variables *)

type vty_value = private {
  vtv_ity   : ity;
  vtv_ghost : bool;
}

val vty_value : ?ghost:bool -> ity -> vty_value

type pvsymbol = private {
  pv_vs   : vsymbol;
  pv_vtv  : vty_value;
  pv_vars : varset;
}

module Mpv : Extmap.S with type key = pvsymbol
module Spv : Extset.S with module M = Mpv
module Hpv : Exthtbl.S with type key = pvsymbol
module Wpv : Weakhtbl.S with type key = pvsymbol

val pv_equal : pvsymbol -> pvsymbol -> bool

val create_pvsymbol : preid -> vty_value -> pvsymbol

val restore_pv : vsymbol -> pvsymbol
  (* raises Not_found if the argument is not a pv_vs *)

val restore_pv_by_id : ident -> pvsymbol
  (* raises Not_found if the argument is not a pv_vs.vs_name *)

(** program types *)

type vty =
  | VTvalue of vty_value
  | VTarrow of vty_arrow

and vty_arrow = private {
  vta_args   : pvsymbol list;
  vta_result : vty;
  vta_spec   : spec;
  vta_ghost  : bool;
}

exception UnboundException of xsymbol

(* every raised exception must have a postcondition in spec.c_xpost *)
val vty_arrow : pvsymbol list -> ?spec:spec -> ?ghost:bool -> vty -> vty_arrow

(* this only compares the types of arguments and results, and ignores
   the spec. In other words, only the type variables and regions in
   [vta_vars vta] are matched. The caller should supply a "freezing"
   substitution that covers all external type variables and regions. *)
val vta_vars_match : ity_subst -> vty_arrow -> vty_arrow -> ity_subst

(* the substitution must cover not only [vta_vars vta] but
   also every type variable and every region in vta_spec *)
val vta_full_inst : ity_subst -> vty_arrow -> vty_arrow

(* remove from the given arrow every effect that is covered
   neither by the arrow's arguments nor by the given varmap *)
val vta_filter : varmap -> vty_arrow -> vty_arrow

(* apply a function specification to a variable argument *)
val vta_app : vty_arrow -> pvsymbol -> spec * vty

(* test for ghostness and convert to ghost *)
val vty_ghost : vty -> bool
val vty_ghostify : vty -> vty

(* verify that the spec corresponds to the result type *)
val spec_check : spec -> vty -> unit

(* convert arrows to the unit type *)
val ity_of_vty : vty -> ity
val ty_of_vty  : vty -> ty

(* collects the type variables and regions in arguments and values,
   but ignores the spec *)
val vta_vars : vty_arrow -> varset
val vty_vars : vty -> varset
