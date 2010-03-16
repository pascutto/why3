(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident
open Ty
open Term
open Decl
open Theory2

(** Cloning map *)

type clone

val cloned_from : clone -> ident -> ident -> bool

val clone_tag : clone -> int

(** Task *)

type task = private {
  task_decl  : decl;
  task_prev  : task option;
  task_known : decl Mid.t;
  task_tag   : int;
}

(* constructors *)

val init_task : task

val add_decl : task -> decl -> task

val split_theory : theory -> Spr.t -> (task * clone) list

val split_theory_full : theory -> (task * clone) list

(* bottom-up, tail-recursive traversal functions *)

val task_fold : ('a -> decl -> 'a) -> 'a -> task -> 'a

val task_iter : (decl -> unit) -> task -> unit

val task_decls : task -> decl list

(* exceptions *)

exception UnknownIdent of ident
exception RedeclaredIdent of ident

