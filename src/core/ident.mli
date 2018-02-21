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

(** Identifiers *)

(** {2 Labels} *)

type label = private {
  lab_string : string;
  lab_tag    : int;
}

module Mlab : Extmap.S with type key = label
module Slab : Extset.S with module M = Mlab

val lab_compare : label -> label -> int
val lab_equal : label -> label -> bool
val lab_hash : label -> int

val create_label : string -> label

val list_label: unit -> string list

(** {2 Naming convention } *)

val infix: string -> string
(** Apply the naming convention for infix operator (+) *)

val prefix: string -> string
(** Apply the naming convention for prefix operator *)

val mixfix: string -> string
(** Apply the naming convention for mixfix operator *)

val kind_of_fix: string -> [ `None
                           | `Prefix of string
                           | `Infix  of string
                           | `Mixfix of string ]

(** {2 Identifiers} *)

type ident = private {
  id_string : string;               (** non-unique name *)
  id_label  : Slab.t;               (** identifier labels *)
  id_loc    : Loc.position option;  (** optional location *)
  id_tag    : Weakhtbl.tag;         (** unique magical tag *)
}

module Mid : Extmap.S with type key = ident
module Sid : Extset.S with module M = Mid
module Hid : Exthtbl.S with type key = ident
module Wid : Weakhtbl.S with type key = ident

val id_compare : ident -> ident -> int
val id_equal : ident -> ident -> bool
val id_hash : ident -> int

(** a user-created type of unregistered identifiers *)
type preid = {
  pre_name  : string;
  pre_label : Slab.t;
  pre_loc   : Loc.position option;
}

(** register a pre-ident (you should never use this function) *)
val id_register : preid -> ident

(** create a fresh pre-ident *)
val id_fresh : ?label:Slab.t -> ?loc:Loc.position -> string -> preid

(** create a localized pre-ident *)
val id_user : ?label:Slab.t -> string -> Loc.position -> preid

(** create a duplicate pre-ident with given labels *)
val id_lab : Slab.t -> ident -> preid

(** create a duplicate pre-ident *)
val id_clone : ?label:Slab.t -> ident -> preid

(** create a derived pre-ident (inherit labels and location) *)
val id_derive : ?label:Slab.t -> string -> ident -> preid

(* DEPRECATED : retrieve preid name without registering *)
val preid_name : preid -> string

(** Unique persistent names for pretty printing *)

type ident_printer

val create_ident_printer :
  ?sanitizer : (string -> string) -> string list -> ident_printer
(** start a new printer with a sanitizing function and a blacklist *)

val id_unique :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** use ident_printer to generate a unique name for ident
    an optional sanitizer is applied over the printer's sanitizer *)

val string_unique : ident_printer -> string -> string
(** Uniquify string *)

val known_id: ident_printer -> ident -> bool
(** Returns true if the printer already knows the id.
    false if it does not. *)

val forget_id : ident_printer -> ident -> unit
(** forget an ident *)

val forget_all : ident_printer -> unit
(** forget all idents *)

val sanitizer' : (char -> string) -> (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first and last letter *)

val sanitizer : (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first letter *)

(** various character encoders *)

val char_to_alpha : char -> string
val char_to_lalpha : char -> string
val char_to_ualpha : char -> string
val char_to_alnum : char -> string
val char_to_lalnum : char -> string
val char_to_alnumus : char -> string
val char_to_lalnumus : char -> string


(** {2 Name handling for ITP} *)

val id_unique_label :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** Do the same as id_unique except that it tries first to
   use the "name:" label to generate the name instead of id.id_string *)



(** {2 labels for handling counterexamples} *)

val model_label : label
val model_projected_label : label
val model_vc_label : label
val model_vc_post_label : label

val has_a_model_label : ident -> bool
(** [true] when [ident] has one of the labels above. *)

val remove_model_labels : labels : Slab.t -> Slab.t
(** Returns a copy of labels without [model_label] and [model_projected_label]. *)

val create_model_trace_label : string -> label

val is_model_trace_label : label -> bool

val append_to_model_trace_label : labels : Slab.t ->
  to_append : string ->
  Slab.t
(** The returned set of labels will contain the same set of labels
    as argument labels except that a label of the form ["model_trace:*"]
    will be ["model_trace:*to_append"]. *)

val append_to_model_element_name : labels : Slab.t ->
  to_append : string ->
  Slab.t
(** The returned set of labels will contain the same set of labels
    as argument labels except that a label of the form ["model_trace:*@*"]
    will be ["model_trace:*to_append@*"]. *)

val get_model_element_name : labels : Slab.t -> string
(** If labels contain a label of the form ["model_trace:name@*"],
    return ["name"].
    Throws [Not_found] if there is no label of the form ["model_trace:*"]. *)

val get_model_trace_string : labels : Slab.t -> string
(** If labels contain a label of the form ["model_trace:mt_string"],
    return ["mt_string"].
    Throws [Not_found] if there is no label of the form ["model_trace:*"]. *)

val get_model_trace_label : labels : Slab.t -> Slab.elt
(** Return a label of the form ["model_trace:*"].
    Throws [Not_found] if there is no such label. *)
