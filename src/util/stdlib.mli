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

module Map : Extmap.Map
module XHashtbl : Exthtbl.Hashtbl

(* Set, Map, Hashtbl on ints and strings *)

module Mint : Map.S with type key = int
module Sint : Mint.Set
module Hint : XHashtbl.S with type key = int

module Mstr : Map.S with type key = string
module Sstr : Mstr.Set
module Hstr : XHashtbl.S with type key = string

(* Set, Map, Hashtbl on structures with a unique tag *)

module type TaggedType =
sig
  type t
  val tag : t -> int
end

module type OrderedHashedType =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHashed (X : TaggedType) :
  OrderedHashedType with type t = X.t

module OrderedHashedList (X : TaggedType) :
  OrderedHashedType with type t = X.t list

module MakeMSH (X : TaggedType) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : XHashtbl.S with type key = X.t
end

module MakeMSHW (X : Weakhtbl.Weakey) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : XHashtbl.S with type key = X.t
  module W : Weakhtbl.S with type key = X.t
end
