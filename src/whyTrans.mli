(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2015, The IMDEA Software Institute
   Copyright (c) 2015, CRI-MINES ParisTech/PSL Research University

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Parsetree
open Exp
open Why3

(*  *)
type w_env

(* Create a new why environment *)
val new_env : ExpState.exp_st -> w_env

(* Add a new function/constant definition to the environment *)
val add_fdef : w_env -> int -> binder_info -> Ty.ty -> w_env

(* Get the declarations already in the environment *)
val w_decl : w_env -> Why3.Decl.decl list

(* Non-translatable things can be recovered *)
exception BailTranslation

val rtype_to_why3 :          ty  -> Ty.ty
val exp_to_why3   : w_env -> exp -> Term.term


