(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   Copyright (c) 2015, CRI-MINES ParisTech/PSL Research University

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils

open Support.Util

(* -------------------------------------------------------------------- *)
exception ParseError of EcLocation.t * string option

let pp_parse_error fmt msg =
  match msg with
  | Some msg -> Format.fprintf fmt "parse error: %s" msg
  | None     -> Format.fprintf fmt "parse error"

let () =
  let pp fmt exn =
    match exn with
    | ParseError (_loc, msg) -> pp_parse_error fmt msg
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)

(* Is the binder relational? *)
type binder_info = {
  b_rel    : bool;
  b_name   : string;
  b_opaque : bool;                      (* Whether to expand *)
}

(* Dummy _bi *)
let _dbi = { b_rel = false; b_name = "_"; b_opaque = true }

type var_side =
  | SiNone
  | SiLeft
  | SiRight

let swap_side sd = match sd with
  | SiNone  -> SiNone
  | SiLeft  -> SiRight
  | SiRight -> SiLeft

let string_of_side s = match s with
  | SiNone  -> ""
  | SiLeft  -> "1"
  | SiRight -> "2"

type var_info = {
  v_binfo : binder_info;

  (* deBruijn Indexes, first at 0 *)
  v_index : int;

  (* Side for relational variables *)
  v_side  : var_side;

  (* Debug fields *)
  v_size  : int;
}

let var_eq v1 v2 =  v1.v_index = v2.v_index
                 && v1.v_side  = v2.v_side

(* Helper to modify the index *)
let shift_var o n v = { v with
  v_index = if o <= v.v_index then v.v_index + n else v.v_index;
  v_size  = v.v_size  + n;}

(* -------------------------------------------------------------------- *)
(* Expressions *)

(* Int and real builtins *)
type exp_const =
  | ECInt  of int
  | ECReal of float

(* Primitive expressions and types (including constructors) are
   globally named and scoped using a why3 theory
*)
type th_info    = (string * string)
type prim_info  = th_info * string
type cons_info  = th_info * string
type tprim_info = th_info * string

(* Patterns are of the form "Cons v1 v2 v3 ...." so the lenght of the
   list determines the number of variables
*)
type pattern_r = (cons_info * binder_info list)
and pattern = pattern_r located

(* Empty for now *)
type dmonad_type =
| Dsymbol of string

type monad_type =
| PMonad
| CMonad
| DMonad

type exp_r =
  (* Ummm  *)
  | EImport  of th_info * exp

  (* Constants *)
  | EConst   of exp_const

  (* Primitives *)
  | EPrim    of prim_info

  (* Variables *)
  | EVar     of var_info

  (* Functions *)
  | ELam     of binder_info * ty * exp

  (* We support application of the form f@[a;b;c;d] for technical
     reasons related to the communication with the SMT solver, it is
     actually used in the core sometimes.
  *)
  | EApp     of exp * exp list

  (* Let and letrec.

     Do we want an "opaque" field here?
  *)
  (*            binder        trust (VC name)  ann      e1    e2  *)
  | ELet     of binder_info * string option  * ty * exp * exp

  (*            binder        ty   termination   e1    e2  *)
  | EFix     of binder_info * ty * (int * int) option * exp

  (* Constructors: not pleased about the distinction with EPrim *)
  | ECs      of cons_info

  (* Pattern matching with optional return annotation *)
  | EMatch   of bool * exp * (pattern * exp) list * ty option

  (* Distribution/Termination Monads *)
  | EMUnit   of monad_type * exp
  | EMLet    of monad_type * binder_info * ty option * exp * exp

and exp = exp_r located

(* Types *)
and ty_r =

  (* Existential or Unification Variables *)
  | TVar of ty_var ref

  (* Scheme Variables, hacky for now... *)
  | TQVar of string

  (* Primitive types, possibly with arguments *)
  | TPrim    of tprim_info * ty list

  (* Partiality Monad *)
  | TC       of ty

  (* Distribution Type with eps-delta distance *)
  | TM       of exp * exp * ty

  (* Generic Probability Monad *)
  | TG       of dmonad_type * exp * ty

  (* Function and refinement types *)
  | TPi      of binder_info * ty * ty
  | TRef     of binder_info * ty * exp

and ty_var =

  | TV_Free of string
  | TV_Link of ty

(* Types can be annotated with two terms (corresponding to the two
   runs) for refinement. Not sure this is the best strategy but seems
   to work well for now.
*)
and ty = (ty_r * (exp * exp) option) located

(* Refinement formula *)
(* and form_r = *)
(*   | FUnOp    of f_unop  * form *)
(*   | FBinOp   of f_binop * form * form *)
(*   | FQuant   of f_quant * binder_info * ty * form *)
(*   | FPred    of f_pred * exp * exp *)
(* and form   = form_r located *)

(* Generation of fresh type variables *)
let ty_var_fresh =
  let counter = ref 0 in
  fun () ->
    let f = !counter                      in
    incr counter;
    let v_name =  "T" ^ (string_of_int f) in
    TVar (ref (TV_Free v_name))

(* de-annotate type *)
let ty_u ty = fst (unloc ty)

(* get annotation   *)
let ty_e ty = snd (unloc ty)

let erase_ty_ann ty      = lmap (fun (ty_r, _) -> (ty_r, None)) ty
let modify_ty_ann ty ann = lmap (fun (ty_r, _) -> (ty_r, Some ann)) ty

(* Unfortunately we have to define our own structural equality *)

(* We ignore types for now *)
let rec exp_eq e1 e2 = match unloc e1, unloc e2 with
  | EImport (th1, e1)                   , EImport (th2, e2)                   -> th1 = th2        && exp_eq e1 e2
  | EConst c1                           , EConst c2                           -> c1  = c2
  | EPrim s1                            , EPrim s2                            -> s1  = s2
  | ECs cs1                             , ECs cs2                             -> cs1 = cs2
  | EVar v1                             , EVar v2                             -> var_eq v1   v2
  | EMatch (asy1, e1, pl1, _ty1)        , EMatch (asy2, e2, pl2, _ty2)        -> exp_eq e1   e2   && List.for_all2 pat_eq pl1 pl2 && asy1 = asy2
  | ELam (_bi1, _ty1, e1)               , ELam (_bi2, _ty2, e2)               -> exp_eq e1   e2
  | EApp (e1_f, e1_l)                   , EApp (e2_f, e2_l)                   -> exp_eq e1_f e2_f && List.for_all2 exp_eq e1_l e2_l
  | ELet (_, _, _ty1, e1_x, e1_e)       , ELet (_, _, _ty2, e2_x, e2_e)       -> exp_eq e1_x e2_x && exp_eq e1_e e2_e
  | EFix (_, _, tc1, e1_e)              , EFix (_, _, tc2, e2_e)              -> tc1 = tc2        && exp_eq e1_e e2_e
  | EMUnit (mt1, e1)                    , EMUnit (mt2, e2)                    -> mt1 = mt2        && exp_eq e1   e2
  | EMLet (mt1, _, _, e1_x, e1_e)       , EMLet (mt2, _, _, e2_x, e2_e)       -> exp_eq e1_x e2_x && exp_eq e1_e e2_e
  | _                                   , _                                   -> false
(* We don't do any fancy stuff here... *)
and pat_eq (p1, e1) (p2, e2) = match unloc p1, unloc p2 with
  | (cs1, _), (cs2, _) -> cs1 = cs2 && exp_eq e1 e2

and ty_eq ty1 ty2 = match ty_u ty1, ty_u ty2 with

  | TVar {contents = TV_Link t1}, t2              -> ty_eq t1 ty2
  | t1, TVar {contents = TV_Link t2}              -> ty_eq ty1 t2

  | TVar {contents = TV_Free v1},
    TVar {contents = TV_Free v2}                  -> v1 = v2

  | TPrim (n1, a1), TPrim (n2, a2)                -> n1 = n2 && begin
                                                     try List.for_all2 ty_eq a1 a2
                                                     with Invalid_argument _ -> false
                                                     end

  | TC ty1                , TC ty2                -> ty_eq  ty1   ty2
  | TM (a1, d1, ty1)      , TM (a2, d2, ty2)      -> exp_eq a1    a2    && exp_eq d1    d2 && ty_eq ty1 ty2
  | TPi (_, ty_a1, ty_r1) , TPi (_, ty_a2, ty_r2) -> ty_eq  ty_a1 ty_a2 && ty_eq  ty_r1 ty_r2
  | TRef (_, ty1, lexp1)  , TRef (_, ty2, lexp2)  -> ty_eq  ty1   ty2   && exp_eq lexp1 lexp2
  | _                     , _                     -> false

(* Return the number of arrows in ty *)
let rec function_arity ty = match ty_u ty with
  | TPi (_, _, ty_r) -> 1 + function_arity ty_r
  | _                -> 0

(* Folding over expressions/types *)
module Fold = struct

  let omap = Option.map

  (* Types:

     - 'ei_ty  : Information about binders/environment
     - 'e_ty   : Expressions
     - 't_ty   : Types
     - 'pat_ty : Patterns
  *)

  (* Parameters to fold *)
  type ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn = {


    (* Binder builder *)
    f_inc    : binder_info -> ty -> 'ei_ty                                     -> 'ei_ty;

    (* Expressions *)
    f_import : th_info * 'e_ty                                                 -> 'e_ty;
    f_const  : exp_const                                                       -> 'e_ty;
    f_prim   : prim_info                                                       -> 'e_ty;
    f_var    : var_info                                                        -> 'e_ty;
    f_cs     : cons_info                                                       -> 'e_ty;
    f_match  : bool * 'e_ty * ('pat_ty * 'e_ty) list * 't_ty option            -> 'e_ty;
    f_lam    : binder_info * 't_ty * 'e_ty                                     -> 'e_ty;
    f_app    : 'e_ty * 'e_ty list                                              -> 'e_ty;
    f_let    : binder_info * string option * 't_ty * 'e_ty * 'e_ty             -> 'e_ty;
    f_fix    : binder_info * 't_ty * (int * int) option * 'e_ty                -> 'e_ty;
    f_munit  : monad_type * 'e_ty                                              -> 'e_ty;
    f_mlet   : monad_type * binder_info * 't_ty option * 'e_ty * 'e_ty         -> 'e_ty;

    (* Patterns *)
    f_pat    : cons_info * binder_info list                                    -> 'pat_ty;

    (* EVars *)
    f_tvfree : string                                                          -> 't_var;
    f_tvlink : 't_ty                                                           -> 't_var;

    (* Types *)
    f_tvar   : ('e_ty * 'e_ty) option * ty_var ref * 't_var ref                -> 't_ty;
    f_tqvar  : ('e_ty * 'e_ty) option * string                                 -> 't_ty;
    f_tprim  : ('e_ty * 'e_ty) option * tprim_info * 't_ty list                -> 't_ty;
    f_tc     : ('e_ty * 'e_ty) option * 't_ty                                  -> 't_ty;
    f_tm     : ('e_ty * 'e_ty) option * 'e_ty * 'e_ty * 't_ty                  -> 't_ty;
    f_tg     : ('e_ty * 'e_ty) option * dmonad_type * 'e_ty * 't_ty            -> 't_ty;
    f_pi     : ('e_ty * 'e_ty) option * binder_info * 't_ty * 't_ty            -> 't_ty;
    f_ref    : ('e_ty * 'e_ty) option * binder_info * 't_ty * 'e_ty            -> 't_ty;
  }

  (* This is hacky *)
  let ty_or_fv loc ty = match ty with
    | Some ty -> ty
    | None    -> let t_var = ty_var_fresh () in
                 mk_loc loc (t_var, None)

  let rec exp_fold ht (ei : 'ei_ty) (fn_s : t -> 'ei_ty -> ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn) e : 'e_ty =
    let fn     = fn_s (getloc e) ei          in

    match unloc e with

    | EImport (th, e)                         -> fn.f_import (th, exp_fold ht ei fn_s e)
    | EConst c                                -> fn.f_const c
    | EPrim s                                 -> fn.f_prim s
    | ECs cs                                  -> fn.f_cs cs
    | EVar v                                  -> fn.f_var v

    | EMatch (asy, e, pl, ty)                 -> let f_e  = exp_fold ht ei fn_s e              in
                                                 let f_pl = List.map (pat_fold ht ei fn_s) pl     in
                                                 let f_ty = omap (ty_fold ht ei fn_s) ty       in
                                                 fn.f_match (asy, f_e, f_pl, f_ty)

    | ELam (bi, ty, e)                        -> let iei  = fn.f_inc bi  ty ei                 in
                                                 let f_ty = ty_fold ht  ei  fn_s ty            in
                                                 let f_e  = exp_fold ht iei fn_s e             in
                                                 fn.f_lam (bi, f_ty, f_e)

    | EApp (e_f, e_l)                         -> let f_ef = exp_fold ht ei fn_s e_f            in
                                                 let f_el = List.map (exp_fold ht ei fn_s) e_l in
                                                 fn.f_app (f_ef, f_el)

    | ELet (bi, tr, ty, e1, e2)               -> let iei  = fn.f_inc  bi ty ei                 in

                                                 let f_ty = ty_fold ht   ei fn_s ty            in
                                                 let f_e1 = exp_fold ht  ei fn_s e1            in
                                                 let f_e2 = exp_fold ht iei fn_s e2            in
                                                 fn.f_let (bi, tr, f_ty, f_e1, f_e2)

    | EFix (bi, ty, tc, e)                    -> let iei  = fn.f_inc  bi ty ei                 in

                                                 let f_ty = ty_fold ht   ei  fn_s ty           in
                                                 let f_e  = exp_fold ht iei fn_s e             in
                                                 fn.f_fix (bi, f_ty, tc, f_e)

    | EMUnit (mt, e)                          -> fn.f_munit (mt, exp_fold ht ei fn_s e)

    | EMLet (mt, bi, ty_a, e1, e2)            -> let ty   = ty_or_fv (getloc e) ty_a           in
                                                 let iei  = fn.f_inc bi ty ei                  in
                                                 let f_ty = omap (ty_fold ht ei fn_s) ty_a     in
                                                 let f_e1 = exp_fold ht  ei  fn_s e1           in
                                                 let f_e2 = exp_fold ht iei  fn_s e2           in
                                                 fn.f_mlet (mt, bi, f_ty, f_e1, f_e2)

and pat_fold ht ei fn_s (pat, e) : 't_pat =

    let fn     = fn_s (getloc pat) ei                               in

    match unloc pat with
    | (cs, bl) ->
      (* FIXME: We don't have the type for the pattern matching binders,
         should we resolve it parsing time?
      *)
      let pat_ei = List.fold_left ( fun ei bi ->
        let ty = ty_or_fv (getloc pat) None                         in
        fn.f_inc bi ty ei) ei bl                                    in
      let f_e    = exp_fold ht pat_ei fn_s e                        in
      let f_p    = fn.f_pat (cs, bl)                                in
      (f_p, f_e)

and tvar_fold ht loc (ei : 'ei_ty)
            (fn_s : t -> 'ei_ty -> ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn) (tv : ty_var) : 't_var =
    let fn        = fn_s loc ei                                     in

    match tv with
    | TV_Free s  -> fn.f_tvfree s
    | TV_Link ty -> fn.f_tvlink (ty_fold ht ei fn_s ty)

and ty_fold (ht : (ty_var ref, 't_var ref) Hashtbl.t)
            (ei : 'ei_ty)
            (fn_s : t -> 'ei_ty -> ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn) (ty : ty) : 't_ty =

    let loc       = getloc ty                                       in
    let fn        = fn_s (getloc ty) ei                             in
    let (ty, ann) = unloc ty                                        in
    let f_ann     = Option.map (fun (el, er) ->
      (exp_fold ht ei fn_s el, exp_fold ht ei fn_s er)) ann         in

    let open Hashtbl in
    match ty with

    (* XXX: FIXME/CRITICAL, check that we are not losing the
       graph/sharing information here *)
    | TVar tvar -> if mem ht tvar then
                      fn.f_tvar (f_ann, tvar, find ht tvar)
                   else (add ht tvar (ref (tvar_fold ht loc ei fn_s !tvar));
                         fn.f_tvar (f_ann, tvar, find ht tvar))

    | TQVar s               -> fn.f_tqvar (f_ann, s)

    | TPrim(tc, targs)      -> fn.f_tprim (f_ann, tc, List.map (ty_fold ht ei fn_s) targs)

    | TC    ty              -> fn.f_tc (f_ann, ty_fold ht ei fn_s ty)

    | TM   (a, d, ty)       -> let f_a  = exp_fold ht ei fn_s a     in
                               let f_d  = exp_fold ht ei fn_s d     in
                               let f_ty = ty_fold  ht ei fn_s ty    in
                               fn.f_tm (f_ann, f_a, f_d, f_ty)

    | TG   (mty, e, ty)     -> let f_e  = exp_fold ht ei fn_s e     in
                               let f_ty = ty_fold  ht ei fn_s ty    in
                               fn.f_tg (f_ann, mty, f_e, f_ty)
    | TPi  (bi, ty_a, ty_r) -> let iei  = fn.f_inc bi ty_a ei       in
                               let f_a  = ty_fold ht  ei  fn_s ty_a in
                               let f_r  = ty_fold ht iei  fn_s ty_r in
                               fn.f_pi (f_ann, bi, f_a, f_r)

    | TRef (bi, ty, lexp)   -> let iei  = fn.f_inc bi ty ei         in
                               let f_ty = ty_fold  ht  ei fn_s ty   in
                               let f_e  = exp_fold ht iei fn_s lexp in
                               fn.f_ref (f_ann, bi, f_ty, f_e)

  (* Hack for doing folds over graphs, our unification variables are
     Ocaml references, so we use a hashtable to cache shared results.
  *)
  let ty_fold (ei : 'ei_ty)
      (fn_s : t -> 'ei_ty -> ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn) (ty : ty) : 't_ty =
    let ht : (ty_var ref, 't_tvar ref) Hashtbl.t = Hashtbl.create 100 in
    ty_fold ht ei fn_s ty

  let exp_fold (ei : 'ei_ty)
      (fn_s : t -> 'ei_ty -> ('ei_ty, 'e_ty, 'pat_ty, 't_ty, 't_var) fold_fn) (e : exp) : 'e_ty =
    let ht : (ty_var ref, 't_tvar ref) Hashtbl.t = Hashtbl.create 100 in
    exp_fold ht ei fn_s e

  (* Default functions for the identity fold *)
  let id_fn inc loc ei : ('ei, exp, pattern, ty, ty_var) fold_fn =
    let l_fn x = mk_loc loc x in {
      f_inc    = inc ;
      f_import = (fun (th, e)                  -> l_fn @@ EImport (th, e));
      f_const  = (fun c                        -> l_fn @@ EConst c);
      f_prim   = (fun p                        -> l_fn @@ EPrim p);
      f_var    = (fun v                        -> l_fn @@ EVar v);
      f_cs     = (fun cs                       -> l_fn @@ ECs cs);
      f_match  = (fun (asy, e, pl, ty)         -> l_fn @@ EMatch (asy, e, pl, ty));
      f_lam    = (fun (b, ty, e)               -> l_fn @@ ELam (b, ty, e));
      f_app    = (fun (e_f, e_l)               -> l_fn @@ EApp (e_f, e_l));
      f_let    = (fun (bi, b, ty, e1, e2)      -> l_fn @@ ELet (bi, b, ty, e1, e2));
      f_fix    = (fun (bi, ty, tc, e)          -> l_fn @@ EFix (bi, ty, tc, e));
      f_munit  = (fun (mt, e)                  -> l_fn @@ EMUnit (mt, e));
      f_mlet   = (fun (mt, bi, ty_a, e1, e2)   -> l_fn @@ EMLet (mt, bi, ty_a, e1, e2));

      (* Patterns *)
      f_pat    = (fun (cs, bl)                 -> l_fn (cs, bl));

      (* EVars *)
      f_tvfree = (fun s                        -> TV_Free s);
      f_tvlink = (fun ty                       -> TV_Link ty);

      (* Types *)
      f_tvar   = (fun (ann, tv, _s)            -> l_fn (TVar tv, ann));
      f_tqvar  = (fun (ann, s)                 -> l_fn (TQVar s, ann));
      f_tprim  = (fun (ann, typ, tyargs)       -> l_fn (TPrim (typ, tyargs), ann));
      f_tc     = (fun (ann, tyc)               -> l_fn (TC tyc, ann));
      f_tm     = (fun (ann, e_a, e_b, ty)      -> l_fn (TM (e_a, e_b, ty), ann));
      f_tg     = (fun (ann, mty, e_d, ty)      -> l_fn (TG (mty, e_d, ty), ann));
      f_pi     = (fun (ann, bi, ty_a, ty_r)    -> l_fn (TPi (bi, ty_a, ty_r), ann));
      f_ref    = (fun (ann, bi, ty_r, e)       -> l_fn (TRef (bi, ty_r, e), ann));
    }

  (* Functions for a fold with a default *)
  let def_fn (inc : binder_info -> ty -> 'ei_ty -> 'ei_ty)
             (d : 'r_ty)
             _lc
             ei
             : ('ei_ty, 'r_ty, 'r_ty, 'r_ty, 'r_ty) fold_fn = {
    f_inc    = inc;
    f_import = (fun _i    -> d);
    f_const  = (fun _c    -> d);
    f_prim   = (fun _p    -> d);
    f_var    = (fun _v    -> d);
    f_cs     = (fun _cs   -> d);
    f_match  = (fun _mi   -> d);
    f_lam    = (fun _li   -> d);
    f_app    = (fun _ai   -> d);
    f_let    = (fun _li   -> d);
    f_fix    = (fun _lri  -> d);
    f_munit  = (fun _ui   -> d);
    f_mlet   = (fun _mli  -> d);

    (* Patterns *)
    f_pat    = (fun _pi   -> d);

    (* EVars *)
    f_tvfree = (fun _s    -> d);
    f_tvlink = (fun _ty   -> d);

    (* Types *)
    f_tvar   = (fun _rv   -> d);
    f_tqvar  = (fun _s    -> d);
    f_tprim  = (fun _ity  -> d);
    f_tc     = (fun _tyc  -> d);
    f_tm     = (fun _tym  -> d);
    f_tg     = (fun _tyg  -> d);
    f_pi     = (fun _typ  -> d);
    f_ref    = (fun _tyr  -> d);
  }

end

open Fold

(*************************************************************************)
(* Get the codomain of a type                                            *)
let fn_codomain loc ei =
  let id _ _ x = x            in
  { (id_fn id loc ei) with
    f_pi     = (fun (_ann, _bi, _ty_a, ty_r) -> ty_r);

    (* We can have refinements of HO types *)
    f_ref    = (fun (_ann, _bi, ty_r, _e)    -> ty_r);
  }

let ty_codomain ty =
  ty_fold 0 fn_codomain ty

(*************************************************************************)
(* Uncurring/flattening of the expression tree                           *)

(* First we fold to get information of the application *)
let fn_uncurry loc ei =
  let id _ _ x = x            in
  let l_fn x   = mk_loc loc x in
  { (id_fn id loc ei) with

    (* Examine nested applications *)
    f_app = (fun (f_e1, f_e2) ->
      match unloc f_e1 with
      | EApp (f, e_l) -> l_fn @@ EApp (f,  e_l @ f_e2)
      | _             -> l_fn @@ EApp (f_e1, f_e2)
    );
  }

let exp_uncurry e =
  exp_fold 0 fn_uncurry e

let ty_uncurry ty =
  ty_fold 0 fn_uncurry ty

(*************************************************************************)
(* Skeleton of a type                                                    *)
let fn_skel loc ei =
  let id _ _ x = x            in
  { (id_fn id loc ei) with

    (* Remove the refinements *)
    (* FIXME: Should we try to keep the annotation? *)
    f_ref    = (fun (ann, bi, ty_r, e)       -> ty_r);
  }

let ty_skel ty =
  ty_fold 0 fn_skel ty

(*************************************************************************)
(* Free expression variables of a type/expression                        *)

let union_list_iset l = List.fold_left IntSet.union IntSet.empty l

let varset_fn loc ei : (int, IntSet.t, IntSet.t, IntSet.t, IntSet.t) Fold.fold_fn =
  let inc _ _ x = x + 1                    in
  let oe t = Option.default IntSet.empty t in
  let ol t = Option.map_default (fun t -> [t]) [] t in

  let open Fold in

  {(def_fn inc IntSet.empty loc ei) with
    f_var    = (fun v                         ->
      if v.v_index >= ei then
        IntSet.singleton (v.v_index - ei)
      else
        IntSet.empty);
    f_match  = (fun (_asy, e, pl, ty)           -> let pe = List.map fst pl in
                                                   union_list_iset ([e] @ (ol ty) @ pe));
    f_lam    = (fun (_b, ty, e)                 -> union_list_iset [ty; e]);
    f_app    = (fun (e_f, e_l)                  -> union_list_iset (e_f :: e_l));
    f_let    = (fun (_bi, _b, ty, e1, e2)       -> union_list_iset [ty; e1; e2]);
    f_fix    = (fun (_b1, ty, _tc, e)           -> union_list_iset [ty; e]);
    f_munit  = (fun (_mt, e)                    -> e);
    f_mlet   = (fun (_mt, _bi, ty_a, e1, e2)    -> union_list_iset [oe ty_a; e1; e2]);

    (* Types *)
    f_tprim  = (fun (_ann, tyc, tyargs)         -> union_list_iset tyargs);
    f_tc     = (fun (_ann, tyc)                 -> tyc);
    f_tm     = (fun (_ann, e_a, e_b, ty)        -> union_list_iset [e_a; e_b; ty]);
    f_pi     = (fun (_ann, _bi, ty_a, ty_r)     -> union_list_iset [ty_a; ty_r]);
    f_ref    = (fun (_ann, _bi, ty_r, e)        -> union_list_iset [ty_r; e]);
  }

let exp_free_vars exp =
  Fold.exp_fold 0 varset_fn exp

let ty_free_vars ty =
  Fold.ty_fold 0 varset_fn ty

(*************************************************************************)
(* Operations on variables *)

let mk_var_fn loc ei (f : int -> var_info -> exp_r) =
  let inc _ _ x = x + 1 in
  let l_fn = mk_loc loc in
  { (id_fn inc loc ei) with
    f_var = (fun v -> l_fn @@ f ei v);
  }

(*************************************************************************)
(* Shifting *)

let f_var_shift o n    nb v = EVar (shift_var (o + nb) n v)
let fn_shift    o n lc ei   = mk_var_fn lc ei (f_var_shift o n)

let exp_shift o n e  = exp_fold 0 (fn_shift o n) e
let ty_shift  o n ty = ty_fold  0 (fn_shift o n) ty

(*************************************************************************)
(* Projection and swapping *)

(* Project (unprojected) relational variables to a side *)
let f_project side _ v =
  let nv = if v.v_binfo.b_rel && v.v_side = SiNone then
      {v with v_side = side}
    else
      v in
  EVar nv

let fn_project       side lc ei = mk_var_fn lc ei (f_project side)

let exp_project_side side e = exp_fold 0 (fn_project side) e
let exp_project           e = exp_project_side SiLeft  e,
                              exp_project_side SiRight e


(* Unprojects x *)
let f_unproject n x v =
  let nv = if (x+n) = v.v_index then
      {v with v_side = SiNone ; v_binfo = { v.v_binfo with b_rel = false } }
  else
    v
  in EVar nv

let fn_unproject x lc ei = mk_var_fn lc ei (f_unproject x)
let exp_unproject x e = exp_fold 0 (fn_unproject x) e

(* Project (unprojected) relational variables to a side *)
let f_swap _ v =
  let nv = if v.v_binfo.b_rel then
      {v with v_side = swap_side v.v_side}
    else
      v in
  EVar nv

let fn_swap       lc ei = mk_var_fn lc ei f_swap

let exp_swap e  = exp_fold 0  fn_swap e
let ty_swap  ty = ty_fold  0  fn_swap ty

(*************************************************************************)
(* Substitution *)

(* Substitution for both relational and non-relational variables. *)
let f_subst_shift x t n v =
  if (x+n) = v.v_index then

    (* Match! We now check if the binder is relational. *)
    let t = exp_shift 0 n t in

    if v.v_binfo.b_rel then
      (* Format.printf "Projecting var %s" (v.v_binfo.b_name) *)
      unloc (exp_project_side v.v_side t)
(*
      match v.v_side with
      (* We need to project *)
      | SiLeft  -> unloc (project_vars_exp SiLeft  t)
      | SiRight -> unloc (project_vars_exp SiRight t)

      (* No need to project (in an exp) *)
      | SiNone  -> unloc t
*)
    else
      (* Non-relational variable, no need to project *)
      unloc t
  else
    EVar (shift_var (x+n) (-1) v)

let fn_subst  x t lc ei = mk_var_fn lc ei (f_subst_shift x t)

(* e[x/t] *)
let exp_subst x t e  = exp_fold 0 (fn_subst x t) e
let ty_subst  x t ty = ty_fold  0 (fn_subst x t) ty

(*************************************************************************)
(* Return the list of schema variables in a type                         *)

(* Free quantified variables *)
let union_list_sset l = List.fold_left StrSet.union StrSet.empty l

let qvarset_fn loc ei : (int, StrSet.t, StrSet.t, StrSet.t, StrSet.t) Fold.fold_fn =
  let inc _ _ x = x + 1                    in
  let oe t = Option.default StrSet.empty t in
  let ol t = Option.map_default (fun t -> [t]) [] t in

  let open Fold in

  {(def_fn inc StrSet.empty loc ei) with

    f_match  = (fun (_asy, e, pl, ty)           -> let pe = List.map fst pl in
                                                   union_list_sset ([e] @ (ol ty) @ pe));
    f_lam    = (fun (_b, ty, e)                 -> union_list_sset [ty; e]);
    f_app    = (fun (e_f, e_l)                  -> union_list_sset (e_f :: e_l));
    f_let    = (fun (_bi, _b, ty, e1, e2)       -> union_list_sset [ty; e1; e2]);
    f_fix    = (fun (_b1, ty, _tc, e)           -> union_list_sset [ty; e]);
    f_munit  = (fun (_mt, e)                    -> e);
    f_mlet   = (fun (_mt, _bi, ty_a, e1, e2)    -> union_list_sset [oe ty_a; e1; e2]);

    (* Types *)
    f_tqvar  = (fun (_ann, v)                   -> StrSet.add v StrSet.empty);
    f_tprim  = (fun (_ann, tyc, tyargs)         -> union_list_sset tyargs);
    f_tc     = (fun (_ann, tyc)                 -> tyc);
    f_tm     = (fun (_ann, e_a, e_b, ty)        -> union_list_sset [e_a; e_b; ty]);
    f_pi     = (fun (_ann, _bi, ty_a, ty_r)     -> union_list_sset [ty_a; ty_r]);
    f_ref    = (fun (_ann, _bi, ty_r, e)        -> union_list_sset [ty_r; e]);
  }

let ty_free_qvars ty =
  Fold.ty_fold 0 qvarset_fn ty

(* Subst for qvars *)
let fn_qvar (f : string -> ty_r) loc ei =
  let inc _ _ x = x + 1 in
  let l_fn = mk_loc loc in
  { (id_fn inc loc ei) with
    f_tqvar = (fun (ann, s) -> l_fn @@ (f s, ann));
  }

let ty_qmap subst ty = ty_fold 0 (fn_qvar subst) ty

let ty_instantiate ty =
  let fv      = StrSet.elements @@ ty_free_qvars ty            in
  let freshv  = List.map (fun v -> (v, ty_var_fresh ())) fv    in
  let subst v = begin
    try List.assoc v freshv
    with | Not_found -> raise (Support.Error.Internal ("WTH_" ^ v ))
  end in
  ty_qmap subst ty

(*
let ity_instantiate_list ity_l =
  let fv_l    = List.map ity_fv ity_l                          in
  let fv      = QVarSet.elements @@ List.fold_left
    (fun vs1 vs2  -> QVarSet.union vs1 vs2) QVarSet.empty fv_l in
  let freshv  = List.map (fun v -> (v, ity_var_fresh ())) fv   in
  let subst v = List.assoc v freshv                            in
  List.map (ity_map subst) ity_l
*)


(* Erasure not implemented yet

let ty_erase loc ei =
  let inc _ _ x = x + 1                    in

  let open Fold in
  {(def_fn inc (BT_QVar "-d") loc ei) with
    (* Types *)
    f_ity    = (fun ity                         -> BT_QVar "a");
    f_tprim  = (fun (_ann, typ)                 -> typ);
    f_tc     = (fun (_ann, tyc)                 -> BT_C tyc);
    f_tm     = (fun (_ann, _e_a, _e_b, tym)     -> BT_M tym);
    f_pi     = (fun (_ann, _bi, ty_a, ty_r)     -> BT_Fun (ty_a, ty_r));
    f_ref    = (fun (_ann, _bi, ty_r, _e)       -> ty_r);
  }

*)
