(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

module type S = sig

  type key

  type 'a t

  val create : int -> 'a t
    (* create a hashtbl with weak keys *)

  val clear : 'a t -> unit

  val copy : 'a t -> 'a t

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val remove : 'a t -> key -> unit
    (* remove the value *)

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val iterk : (key -> unit) -> 'a t -> unit

  val foldk : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val length : 'a t -> int

  val memoize : int -> (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_rec : int -> ((key -> 'a) -> (key -> 'a)) -> (key -> 'a)
    (* create a memoizing recursive function *)

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

type tag = int

let create_tag i = i

let dummy_tag = min_int

let tag_equal : tag -> tag -> bool = (==)

let tag_hash k = assert (k != dummy_tag); k

module type Weakey =
sig
  type t
  val tag : t -> tag
end

module Make (S : Weakey) : S with type key = S.t = struct

  module H = Ephemeron.K1.MakeSeeded(struct
      type t = S.t
      let equal s1 s2 = S.tag s1 == S.tag s2
      let hash (_seed: int) x = S.tag x
    end)

  include H

  let create size = create ~random:false size

  let set = replace

  let iterk f h = iter (fun k _ -> f k) h
  let foldk f h acc = fold (fun k _ acc -> f k acc) h acc

  let memoize n fn =
    let h = create n in fun e ->
      try find h e
      with Not_found ->
        let v = fn e in
        set h e v;
        v

  let memoize_rec n fn =
    let h = create n in
    let rec f e =
      try find h e
      with Not_found ->
        let v = fn f e in
        set h e v;
        v
    in
    f

  let memoize_option n fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end

