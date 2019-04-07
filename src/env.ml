(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   Copyright (c) 2018, MINES ParisTech
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Parsetree

(* ---------------------------------------------------------------------- *)
(* Context management *)

(* HO (deBruijn-indexed) environments *)
module HO = struct

  type env = (binder_info * ty) list

  let empty = []

  let length env = List.length env

  let bi_shift o n (bi, ty) =
    (bi, ty_shift o n ty)

  (* Return a binding if it exists. Let the caller handle the error. *)
  let rec slookup idx id env =
    match env with
      []                -> None
    | (bi, ty) :: l ->
      if bi.b_name = id then
	Some (idx, bi, ty)
      else
	slookup (idx+1) id l

  let lookup id env = slookup 0 id env

  let rec env_shift o n env = match env with
      []          -> []
    | bi :: l     -> (bi_shift o n bi) :: env_shift o n l

  (* Extend the environment with a new binding. Shift variables! *)
  let extend name rel opaque ty env =
    let bi = {
      b_rel    = rel;
      b_name   = name;
      b_opaque = opaque;
    }                                           in
    let res = env_shift 0 1 ((bi, ty) :: env)   in
    (bi, res)

  let extend_bi bi ty env =
    env_shift 0 1 ((bi, ty) :: env)

  (* Access a binding *)
  let access ctx i = List.nth ctx i

  let swap_side ctx = List.map (fun (bi, ty) -> (bi, ty_swap ty)) ctx

end

(* First-order enviroments (name-indexed) *)

module FO = struct

  module IdMap = Map.Make(struct
    type t      = string
    let compare = Pervasives.compare
  end)

  type env = {
    (* XXX *)
    prims    : (th_info * ty)             IdMap.t;
    cons     : (th_info * ty)             IdMap.t;
    types    : (th_info * cons_info list) IdMap.t;
    theories : th_info list;
  }

  let empty = {
    prims    = IdMap.empty;
    cons     = IdMap.empty;
    types    = IdMap.empty;
    theories = [];
  }

  exception AlreadyUsed of string

  let add_prim e (th, p) ty = { e with
    prims =
      if IdMap.mem p e.prims then
        raise (AlreadyUsed p)
      else
        IdMap.add p (th, ty) e.prims;
  }

  (* Look up the type of a primitive *)
  let lookup_prim e p = IdMap.find p e.prims

  let add_cons e (th, cs) cs_ty = { e with
    cons =
      if IdMap.mem cs e.cons then
        raise (AlreadyUsed cs)
      else
        IdMap.add cs (th, cs_ty) e.cons;
  }
  (* Return constructor type *)
  let lookup_cons e c = IdMap.find c e.cons

  (* Both type and constructors *)
  let add_type e (th, ty) csl = { e with
    types =
      if IdMap.mem ty e.types then
        raise (AlreadyUsed ty)
      else
        IdMap.add ty (th, csl) e.types;
  }

  (* Return type constructors *)
  let lookup_type e ty = IdMap.find ty e.types

  let add_theory e th = { e with
    theories = e.theories @ [th]
  }

end

(* We carry both FO and HO enviroments *)
type env = {
  ho_env : HO.env;
  fo_env : FO.env;
}

let empty = {
  ho_env = HO.empty;
  fo_env = FO.empty;
}

let get_bindings e = e.ho_env

let length   e = HO.length e.ho_env
let lookup s e = HO.lookup s e.ho_env

let extend s rel opaque ty e =
  let (bi, n_env) = HO.extend s rel opaque ty e.ho_env in
  (bi, {e with ho_env = n_env;})

let extend_bi bi ty e =
  let n_env = HO.extend_bi bi ty e.ho_env in
  {e with ho_env = n_env;}

let access e idx = HO.access e.ho_env idx

(* Why3 primitives *)
let add_prim e p ty = {e with fo_env = FO.add_prim e.fo_env p ty;}
let lookup_prim e = FO.lookup_prim e.fo_env
let all_prims e = FO.IdMap.bindings e.fo_env.FO.prims

(* Why3 constructors *)
let add_cons e c ty = {e with fo_env = FO.add_cons e.fo_env c ty;}
let lookup_cons e = FO.lookup_cons e.fo_env
let all_cons e = FO.IdMap.bindings e.fo_env.FO.cons

(* Why3 types *)
let add_type e ty csl = {e with fo_env = FO.add_type e.fo_env ty csl;}
let lookup_type e = FO.lookup_type e.fo_env
let all_types e = FO.IdMap.bindings e.fo_env.FO.types

let add_theory   e th = {e with fo_env = FO.add_theory e.fo_env th;}
let all_theories e    = e.fo_env.FO.theories

let swap_side e    = {e with ho_env = HO.swap_side e.ho_env;}

