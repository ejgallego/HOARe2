(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Parsetree

type env

val empty  : env
val length : env -> int
val get_bindings : env -> (binder_info * ty) list

val lookup    : string -> env  -> (int * binder_info * ty) option

val extend    : string -> bool -> bool -> ty -> env -> (binder_info * env)
val extend_bi : binder_info -> ty -> env -> env

val access    : env -> int -> (binder_info * ty)

val add_prim    : env -> prim_info -> ty -> env
val lookup_prim : env -> string -> (th_info * ty)
val all_prims   : env -> (string * (th_info * ty)) list

val add_cons    : env -> cons_info -> ty -> env
val lookup_cons : env -> string -> (th_info * ty)

(* All of the constructors *)
val all_cons    : env -> (string * (th_info * ty)) list

(* List of constructors for a type *)
val add_type    : env -> prim_info -> cons_info list -> env
val lookup_type : env -> string -> (th_info * cons_info list)

(* All of the types *)
val all_types   : env -> (string * (th_info * cons_info list)) list

val add_theory   : env -> th_info -> env
val all_theories : env -> th_info list

val swap_side : env -> env
