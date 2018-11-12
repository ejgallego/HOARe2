(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* #use "topfind";; *)
(* #require "why3";; *)

(* #load "whyCore.cmo";; *)
(* #load "support.cmo";; *)
(* #load "ecLocation.cmo";; *)

open Env

module L  = EcLocation
module P  = Print
module O  = Option
module EC = Constants
module PT  = Parsetree

module WEnv = Why3.Env
module WT   = Why3.Theory
module WP   = Why3.Pretty
module WI   = Why3.Ident

module I    = Why3.Ident
module T    = Why3.Term
module Ty   = Why3.Ty

open Why3

module Opts = Support.Options

let _d    = L.mk_loc L._dummy @@ ()
let _dl l = L.mk_loc L._dummy @@ l

open Support.Error

let why_error   fi = error_msg Opts.SMT fi
(* let why_warning fi = message 1 Opts.SMT fi *)
(* let why_info    fi = message 2 Opts.SMT fi *)
(* let why_info2   fi = message 3 Opts.SMT fi *)
let why_debug   fi = message 4 Opts.SMT fi
(* let why_debug2  fi = message 5 Opts.SMT fi *)
let why_debug3  fi = message 6 Opts.SMT fi

(* let tv_n tv = tv.Ty.tv_name.WI.id_string *)
let ts_n ts = ts.Ty.ts_name.WI.id_string
let ls_n ls = ls.T.ls_name.WI.id_string

(************************************************************************)
(* List of ity to ty conversion                                         *)

let iloc t = L.mk_loc L._internal t

(* XXX: Replace iloc for the actual loc *)
let rec desugar_primtypes ty : PT.ty =
  let open PT in
  match ty_u ty with
  | PT.TPrim ((_, "distr"), [l]) ->
    let zero = iloc @@ EConst (ECReal 0.0) in
    iloc @@ (TM (zero, zero, desugar_primtypes l), None)
  | PT.TPrim ((_, "func"), [l1; l2]) ->
    iloc @@ (TPi (_dbi, desugar_primtypes l1, desugar_primtypes l2), None)
  | PT.TPrim (cs, ty_l) ->
    iloc @@ (PT.TPrim(cs, List.map desugar_primtypes ty_l), None)
  | _ -> ty

let rec why3_to_ty (ityl : PT.ty_r list) : PT.ty =
  match ityl with
  | []      -> raise (Internal "ity_to_ty: Empty type?")
  | [x]     -> desugar_primtypes @@ iloc (x, None)
  | x :: xs -> iloc @@ (PT.TPi (PT._dbi, desugar_primtypes (iloc (x, None)), why3_to_ty xs), None)

(* From w3.ty to ity, must mangle some types *)
let ty_freevars_list ty_l = List.fold_left (fun tv_s ty ->
  Ty.ty_freevars tv_s ty) Ty.Stv.empty ty_l

let rec import_w3_ty_core env tv_map ty = match ty.Ty.ty_node with
  | Ty.Tyvar tv        ->
    begin
      try Ty.Mtv.find tv tv_map
      with Not_found ->
        why_error _d "Error importing ty_var!!!"
    end
  | Ty.Tyapp (s, ty_l) ->
    begin
      let ty_n    = ts_n s                                         in
      try let (th, _) = lookup_type env ty_n                       in
          PT.TPrim ((th, ty_n), List.map
            (fun ty -> _dl (import_w3_ty_core env tv_map ty, None)) ty_l)
      with Not_found ->
        why_error _d "Type %s not found!" ty_n
    end

(* Builds a map for every tvariable *)
let build_tv_map tv_set = fst @@
  Ty.Stv.fold (fun tv (tv_map, n) ->
    let n_v  = "a" ^ (string_of_int n)                                                 in
    let n_iv = Parsetree.TQVar n_v                                                     in
    (Ty.Mtv.add tv n_iv tv_map, n + 1)) tv_set (Ty.Mtv.empty, 0)

(* let import_w3_ty env ty =
 *   let ty_fv  = Ty.ty_freevars Ty.Stv.empty ty                                          in
 *   let tv_map = build_tv_map ty_fv                                                      in
 *   import_w3_ty_core env tv_map ty *)

(* let import_w3_ty_l env ty_l =
 *   let ty_fv  = ty_freevars_list ty_l                                                   in
 *   let tv_map = build_tv_map ty_fv                                                      in
 *   List.map (import_w3_ty_core env tv_map) ty_l *)

let import_lsymbol th add ls env =
  (* Get all type variables from arguments and possibly result *)
  let ty_fv_a = ty_freevars_list ls.T.ls_args                                          in
  let ty_fv   = O.map_default (Ty.ty_freevars ty_fv_a) ty_fv_a ls.T.ls_value           in
  let tv_map  = build_tv_map ty_fv                                                     in

  let args_ty = List.map (import_w3_ty_core env tv_map) ls.T.ls_args                   in
  let ret_ty  = O.map_default (import_w3_ty_core env tv_map) EC.typ_prop ls.T.ls_value in
  let l_name  = ls_n ls                                                                in
  let r_type  = why3_to_ty @@ args_ty @ [ret_ty]                                       in
  add env (th, l_name) r_type

(* Name plus constructors *)
let import_ddecl th (tys, csl) env =
  let cs_names = List.fold_left (fun cn  (ls, _proj) -> (th, ls_n ls) :: cn) [] csl    in
  let ty_env   = add_type env (th, (ts_n tys)) cs_names                                in
  List.fold_left (fun env (ls, _projs) ->
    why_debug _d "Importing Constructor: @[%a@]" WP.print_ls ls;
    import_lsymbol th add_cons ls env
  ) ty_env csl

(* "Abstract" types constructors *)
let import_tydecl th ts env =
  add_type env (th, (ts_n ts)) []

(* Add a Why3 Decl to our environment *)
let import_decl th d env =

  match d.Decl.d_node with

  (* Those two are handled in a similar way *)
  (* Abstract predicates and functions *)
  | Decl.Dparam ls ->
        why_debug _d "!I! Importing: @[%a@]" WP.print_param_decl ls;
        import_lsymbol th add_prim ls env

  (* Defined predicates *)
  | Decl.Dlogic lls ->
       List.fold_left (fun env (ls, _ldef) ->
         why_debug _d "!I! Importing: @[%a@]" WP.print_param_decl ls;
         import_lsymbol th add_prim ls env) env lls

  (* Inductive data declarations *)
  | Decl.Ddata ddl ->
       (* why_info dummy_e "Start Data @\n"; *)
       List.fold_left (fun env dd ->
         why_debug _d "!I! Importing data decl @[%a@]" WP.print_data_decl dd;
         import_ddecl th dd env
       ) env ddl

  (* Abstract types *)
  | Decl.Dtype ty  ->
       why_debug _d "!I! Importing Type decl @[%a@]" WP.print_ts ty;
       import_tydecl th ty env

  (* We ignore the below for now *)


  (* Lemmas and axioms *)
  | Decl.Dprop pdl ->
        why_debug3 _d "Proposition: @[%a@]" WP.print_prop_decl pdl;
        env

  | Decl.Dind (ids, idl)  ->
       List.iter (fun ild ->
         let idp p f =  WP.print_ind_decl f p in
         why_debug3 _d "DInd: @[%a@]" (idp ids) ild) idl;
       env

let rec import_decls th decls env = match decls with
  | []        -> env
  | (d :: dl) -> let env' = import_decl th d env in
                 import_decls th dl env'

(* Import an actual Why3 theory *)
let import_why3_theory th_i th env =
  let task   = Task.use_export None th                                  in
  let ths    = Ident.Mid.remove th.WT.th_name (Task.used_theories task) in
  let others = Task.used_symbols ths                                    in
  let decls  = Task.local_decls task others                             in
  let d_env  = import_decls th_i decls env                              in
  add_theory d_env th_i

(* Theories not in a file *)
let th_table  = [
  EC.builtin_th, WT.builtin_theory;
  EC.bool_th,    WT.bool_theory;
  EC.ho_th,      WT.highord_theory
]

let resolve_why3_theory th_i =
  (* Try theories not in a file *)
  if List.mem_assoc th_i th_table
  then
    List.assoc th_i th_table
  else begin match WT.tuple_theory_name (snd th_i) with
  | Some n -> WT.tuple_theory n
  | None   ->
    begin
      try EcProvers.get_w3_th [fst th_i] (snd th_i)
      with
        WEnv.LibraryNotFound f -> why_error _d "File not found %s" (List.nth f 0)
      (* TODO: integrate with Exn_printer *)
      | Loc.Located (p, _exn)  -> why_error _d "Why3 problem at %a" Loc.report_position p
    end
  end

let load_why3_theory th_i env =
  why_debug _d "Trying to load: @[%s.%s@]%!" (fst th_i) (snd th_i);
  let th = resolve_why3_theory th_i in
  import_why3_theory th_i th env

