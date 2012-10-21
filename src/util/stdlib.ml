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

module Map = Extmap.Map
module XHashtbl = Exthtbl.Hashtbl

(* Set, Map, Hashtbl on ints and strings *)

module Int = struct
  type t = int
  let compare = Pervasives.compare
  let equal x y = x = y
  let hash x = x
 end

module Mint = Map.Make(Int)
module Sint = Mint.Set
module Hint = XHashtbl.Make(Int)

module Mstr = Map.Make(String)
module Sstr = Mstr.Set
module Hstr = XHashtbl.Make
  (struct
    type t = String.t
    let hash    = (Hashtbl.hash : string -> int)
    let equal   = ((=) : string -> string -> bool)
  end)

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

module OrderedHashed (X : TaggedType) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashedList (X : TaggedType) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
  let compare = Lists.compare cmp_ts
end

module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Map.Make(T)
  module S = M.Set
  module H = XHashtbl.Make(T)
end

module MakeTagged (X : Weakhtbl.Weakey) =
struct
  type t = X.t
  let tag t = Weakhtbl.tag_hash (X.tag t)
end

module MakeMSHW (X : Weakhtbl.Weakey) =
struct
  module T = OrderedHashed(MakeTagged(X))
  module M = Map.Make(T)
  module S = M.Set
  module H = XHashtbl.Make(T)
  module W = Weakhtbl.Make(X)
end
