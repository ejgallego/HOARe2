(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Format

open Parsetree

open Support.Error
open Support.Util

module L    = EcLocation
module E    = Exp
module EC   = Constants
module EB   = E.Builders
module ES   = E.ExpState

module P    = Print
module Opts = Support.Options

module WT   = WhyTransHO
module WP   = Why3.Pretty

module Ev = EvalFast

let as_error   fi   = error_msg Opts.SMT fi

let as_warning fi   = message 1 Opts.SMT fi
let as_info    fi   = message 2 Opts.SMT fi
let as_info2   fi   = message 3 Opts.SMT fi
let as_debug   fi   = message 4 Opts.SMT fi
let as_debug2  fi   = message 5 Opts.SMT fi
let as_debug3  fi   = message 6 Opts.SMT fi

(* Failed assertions *)
let trivial_assertions: int ref         = ref 0
let total_assertions  : int ref         = ref 0
let failed_assertions : exp list ref    = ref []
let pending_vc        : string list ref = ref []

let trust_n           : int ref         = ref 0

(* Assertion checking *)

let pp_wty ppf env =
  P.pp_imap (P.pp_gen_bi WP.print_ty) ppf env

let pp_menv ppf env =
  P.pp_imap P.pp_bi ppf env

(* Imap to (string * a) *)
let pp_sdec pp fmt (s, a) =
  fprintf fmt "@[(%s) %a@]" s pp a

let pp_nimap pp fmt env =
  P.pp_imap (pp_sdec pp) fmt env

(* Normalization of expressions in types *)
let rec ty_norm st ty =
  let nf = Ev.to_nf in
  L.lmap (fun (ty, ann) ->
    (match ty with

    | TPi (bi,            ty_a,              ty_r) ->
      let r_st = ES.open_binder st bi ty_a         in
      TPi (bi, ty_norm st ty_a, ty_norm r_st ty_r)

    | TM (      e_a,       e_d,            ty) ->
      TM (nf st e_a, nf st e_d, ty_norm st ty)

    | TRef(bi,            ty_r,         e_r) ->
      let r_st = ES.open_binder st bi ty_r         in
      TRef(bi, ty_norm st ty_r, nf r_st e_r)

    | ty -> ty
  ), Option.map (fun (el, er) -> (nf st el, nf st er) ) ann) ty

(* Transitive closure of used variables. We perform this check so we
   don't send to the solver unneeded stuff *)
let rec used_vars env prev =
    let next = IntSet.fold (
      fun v s ->
        (* We add the variables transitively used *)
        let v_vs  = ty_free_vars @@ snd @@ RIntMap.find v env in
        (* Now we also add the assumptions where a used variable occur *)
        let v_all = IntSet.union s v_vs in
        RIntMap.fold (fun n (_bi, ty) vs ->
          let ty_vs = ty_free_vars ty in
          if IntSet.is_empty (IntSet.inter ty_vs vs) then
            vs
          else
            IntSet.add n vs
        ) env v_all
    ) prev prev in
    if IntSet.equal next prev then
      next
    else
      used_vars env next

(* Generate the axiom corresponding to a relational type. The first
   argument is the current expression associated to that type.
*)

let rec rtype_to_axiom st ty_exp ty = match ty_u ty with

  (* A HO type will generate a forall, shifting is slightly tricky
     here in order to account for the correct bound variables *)
  | TPi (bi, ty_a, ty_r) ->
    let a_var = L.mk_loc ty.L.pl_loc @@ EVar {
      v_binfo = bi;
      v_index = 0;
      v_side  = SiNone;
      v_size  = -1;
    }                                                     in
    (* We need to shift ty_a as we introduce a_var *)
    let ty_a_sh = ty_shift 0 1 ty_a in
    let a_exp   = rtype_to_axiom st a_var ty_a_sh         in

    (* As we are building the expression for the application, we must
       shift ty_exp *)
    let ty_exp_sh = exp_shift 0 1 ty_exp                  in
    let pi_exp = EB.mk_exp_app ty ty_exp_sh [a_var]       in

    (* ty_r is already shifted! *)
    let r_exp  = rtype_to_axiom st pi_exp ty_r            in

    begin match a_exp, r_exp with
    | _          , None -> None

    | None       , Some r_exp -> Some (
      EB.mk_exp_forall ty bi ty_a r_exp)

    | Some a_exp , Some r_exp -> Some (
      let impl_exp = EB.mk_exp_bin st EC.l_impl a_exp r_exp in
      EB.mk_exp_forall ty bi ty_a impl_exp)
    end

  (* For a refinement we substitute the variable. *)
  | TRef (_, r_ty, fo) ->

    (* The type on ref could be refined *)
    let r_exp = rtype_to_axiom st ty_exp r_ty in

    begin match r_exp with
    | None ->
      let fo_s = exp_subst 0 ty_exp fo in
      Some fo_s

    | Some r_exp -> Some (
      let fo_s     = exp_subst 0 ty_exp fo in
      EB.mk_exp_bin st EC.l_impl r_exp fo_s
    )
    end

  | TM _ -> as_debug2 ty "!A! Ignoring relational axiom  @[%a@] " P.pp_ty ty; None
  | TC _ -> as_debug2 ty "!A! Ignoring monadic axiom  @[%a@] " P.pp_ty ty; None
  (* Type without logical information *)
  | _    -> None

let rtype_to_axiom st n (bi, ty) =
  let a_var = L.mk_loc ty.L.pl_loc @@ EVar {
    v_binfo = bi;
    v_index = n;
    v_side  = SiNone;
    v_size  = -1;
    }
  in
  (* Transparent definition go away *)
  let ax = rtype_to_axiom st a_var ty in
  Option.may (fun ax -> as_debug3 ty "Axiom [%d]: %a" n P.pp_exp ax) ax;
  Option.map (fun ax -> (bi.b_name, ax)) ax

(* We may not be able to translate some fancy HO expressions for now. *)
let try_ty_trans n ty =
  try Some (WT.rtype_to_why3 ty)
  with WT.BailTranslation -> as_warning ty "Bailing on Type [%d]: @[%a@]" n P.pp_ty ty;
                             None

let try_trans w_st i (n, a) =
  try Some (n, WT.formula_to_why3 w_st a)
  with WT.BailTranslation -> as_warning a "Bailing on Axiom [%d/%s]: @[%a@]" i n P.pp_exp a;
                             None

(* Main Routine:

   - Normalize and uncurry the VC and the preconditions.
   - Generate Why3 definitions and axioms from the pres.
   - ?
   - Profit!
*)

let check_assertion st fo =

  incr total_assertions;

  (* Reset the Why3 pretty printer *)
  WP.forget_all ();

  as_info2  fo "************************************************************************";
  as_info2  fo "!A! Starting assertion check...";
  let w_st = WT.new_env st                                                      in

  (* Create a map v_index -> (bi, type) *)
  let (_ho_len, ho_env) = List.fold_left (fun (n, map) bi ->
    (n+1, RIntMap.add n bi map)) (0, RIntMap.empty)
    (Env.get_bindings @@ ES.getenv st)                                          in

  (* Print the starting conditions *)
  as_debug2 fo "!A! Env   : @[%a@]"   pp_menv ho_env;
  as_info   fo "!A! VC    : @[%a@]" P.pp_exp  fo;

  (* Normalization and uncurrying *)
  (* FIXME: Normalization is *painfully* slow, too many shithings *)
  let ho_norm  = ho_env in

  (* We disable for now, we will normalize the expressions themselves *)
  (* EG: ty_norm proved to be extremely expensive! *)
  (* let ho_norm  = RIntMap.map (fun (bi, ty) -> (bi, ty_norm st ty)) ho_env       in *)
  (* let ho_norm  = RIntMap.map (fun (bi, ty) -> (bi, ty_uncurry ty)) ho_norm      in *)

  (* Remove all transparent axioms *)
  let ho_norm  = RIntMap.filter (fun _ (bi, _) -> bi.b_opaque) ho_norm          in

  (* More norm and uncurry *)
  let fo_norm  = Ev.to_nf st fo                                                 in
  let fo_norm  = exp_uncurry fo_norm                                            in

  (* Print the actual environment that we need to use *)
  as_debug  fo "!A! NF-Env: @[%a@]"   pp_menv ho_norm;
  as_debug  fo "!A! NF-VC : @[%a@]"  P.pp_exp fo_norm;

  (* Generate Why3 types for the assumptions *)
  let ho_types = RIntMap.mapi_filter
    (fun n (bi,ty) -> Option.map (fun ty -> (bi, ty)) (try_ty_trans n ty)) ho_norm in
  as_debug  fo "!A! Ty-Env: @[%a@]" pp_wty ho_types;

  (* We now generate the axioms *)
  let ho_axiom = RIntMap.mapi_filter (rtype_to_axiom st) ho_norm                in

  (* EG: We try to normalize here instead in the types *)
  let ho_axiom = RIntMap.map (fun (n, a) -> (n, Ev.to_nf st a)) ho_axiom        in
  let ho_axiom = RIntMap.map (fun (n, a) -> (n, exp_uncurry a)) ho_axiom        in

  (* Print the actual environment that we need to use *)
  as_debug  fo "!A! NF-Ax: @[%a@]" (pp_nimap P.pp_exp) ho_axiom;

  (* Add the bindings to the why3 environment, this will add two
     definitions for relational binders.  *)
  let w_st = RIntMap.fold (fun n (bi, ty) st ->
    WT.add_fdef st n bi ty) ho_types w_st                                       in

  (* Print why3 declarations (debug purposes) *)
  let w_decl = WT.w_decl w_st                                                   in
  as_debug2  fo "!A! Decls: @[<v>%a@]" (P.pp_list WP.print_decl) w_decl;

  (* Translate the axioms in our format to Why3 axioms *)
  let w_axiom  = RIntMap.mapi_filter (try_trans w_st) ho_axiom                  in
  as_info2  fo "!A! NF-Ax: @[%a@]" (pp_nimap WP.print_term) w_axiom;

  (* Translate the VC itself *)
  let res = try begin

  let w_fo     = WT.formula_to_why3 w_st fo_norm                                in
  as_info2  fo "!A! Why-VC: @[%a@]"  WP.print_term w_fo;

  let theories = Env.all_theories (ES.getenv st)                                in

  (* Figure out if we check the assertion externally or not  *)
  let trust = ES.mk_vc_file st !trust_n                                         in

  (* Trick for trust generation *)
  begin
    match trust with
    | None    -> trust_n    := 0
    | Some vc -> pending_vc := !pending_vc @ [vc];
                 incr trust_n
  end;

  if Opts.comp_enabled Opts.SMT then
      ArlcSolver.post trust theories w_decl w_axiom w_fo fo.L.pl_loc
    else
      Some (true, ["admitted"])
  end with
  | WT.BailTranslation ->
    as_warning fo "Backend couldn't translate the VC, (likely cause: unsupported HO terms)";
    None
  in

  begin match res with
  | None ->
    failed_assertions := !failed_assertions @ [fo];
    as_info2 fo "!A! Assertion check end with result unkwown"
  | Some (res , provers) ->
    as_info2  fo "!A! Assertion check end with result: %b by %a" res Format.(pp_print_list pp_print_string) provers
  end;
  as_info2  fo "************************************************************************\n";
  res

let is_true st fo = check_assertion st fo
