(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   Copyright (c) 2015, CRI-MINES ParisTech/PSL Research University

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Parsetree

open Support.Error
open Support.Util

module L    = EcLocation

module E    = Exp
module ES   = E.ExpState
module EB   = E.Builders
module EC   = Constants

module P    = Print
module Opts = Support.Options

(* Type checking for relational refinement types *)

let ho_env e = Env.get_bindings (ES.getenv e)

(* Typing Errors *)
type ty_error_elem =
| TypeMismatch    of ES.exp_st * ty  * ty
| CannotApply     of ty  * ty
| CannotInfer     of exp
| MissingIdent    of string
| WrongBinding    of exp
| WrongShape      of ty  * string
| WrongPattern    of string * int
| WrongCoverage   of string
| WrongAssertion  of ty
| AssertionFail   of ES.exp_st * exp
| Termination     of exp
| PropDisabled

(* Not sure about this yet *)
exception TypeError of ty_error_elem L.located

let ty_seq = ref 0

(* Print typing info, differently depending if we are in an assertion *)
let pp_tyst ppf st =
  let symb = if st.L.pl_desc.ES.in_assertion then
      "s" else "[" in
  Format.fprintf ppf "%s%3d]" symb !ty_seq

let typing_error t  = error_msg    Opts.TypeChecker t
let typing_error_pp = error_msg_pp Opts.TypeChecker

(* Output of the typer for now:

  - Info :  Assertions to be checked.
  - Info+:  High-level subtype calls.
            Refinements
  - Debug:  Typing in/out.
  - Debug2: Environments
  - Debug3: Low level subtype stuff
*)

let ty_warning fi   = message 1 Opts.TypeChecker fi
let ty_info    fi   = message 2 Opts.TypeChecker fi
let ty_info2   fi   = message 3 Opts.TypeChecker fi
let ty_debug   fi   = message 4 Opts.TypeChecker fi
let ty_debug2  fi   = message 5 Opts.TypeChecker fi
let ty_debug3  fi   = message 6 Opts.TypeChecker fi

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

(* Still a mess *)
let new_error    t  e = L.mk_loc (L.getloc  t) e
let new_error_st st e = L.mk_loc (L.getloc st) e

let fail  e     = raise (TypeError e)

(* This is not working well *)
let iwhen b s e = if b then s else fail e

module Subtyping = struct

  let check_assertion st fo =
    let as_err = new_error_st st @@ AssertionFail(st, fo) in

    (* Hack until we clean up the locations stuff *)
    let fo = {fo with L.pl_loc = L.getloc st;}            in

    let result = Assertion.is_true st fo                  in
    let ignore = Opts.(!debug_options.soft_assertions)    in

    match result with
    (* Unknown *)
    | None ->
      ty_warning fo "!!!!! Couldn't prove @[%a@]@\nin env: @[%a@]" P.pp_exp fo P.pp_env (ho_env st);
      if not ignore then fail as_err
    (* If the assertion is proven false, we always bail! *)
    | Some(b_res, _) ->
      if not b_res then fail as_err

  let check_implies st fo1 fo2 =
    let impl_ass = EB.mk_exp_bin st EC.l_impl fo1 fo2 in
    if exp_eq fo1 fo2 then (
      incr Assertion.trivial_assertions;
      ty_debug3 fo1 "*** @[%a@] Optimizing check @[%a@] away." pp_tyst st P.pp_exp impl_ass
    ) else
      check_assertion st impl_ass

  let check_float_le st n1 n2 =
    let le_ass = EB.mk_exp_bin st EC.le_float n1 n2 in
    if exp_eq n1 n2 then (
      incr Assertion.trivial_assertions;
      ty_debug3 n2 "*** @[%a@] Optimizing check @[%a@] away." pp_tyst st P.pp_exp le_ass
    ) else
      check_assertion st le_ass

  (* EG: we should be more generic here really *)
  let build_ref_eq st f e =

    let unit_ty    = EB.mk_ty_unit st None                     in

    let (r_b, r_st)= ES.extend st "u" false true unit_ty       in

    let r_f        = exp_shift 0 1 f                           in
    let r_e        = exp_shift 0 1 e                           in

    let eq_ass     = EB.mk_exp_bin r_st EC.eq_op r_f r_e       in

    (* Build the constraint type *)
    let ref_ty     = EB.mk_ty_ref r_st r_b unit_ty eq_ass None in

    (* Safety check *)
    (* Disabled for now due to mutual definition issues        *)
    (* wf_type r_st ref_ty; *)

    let (n_b, n_st)= ES.extend st "ref_" false true ref_ty     in
    (n_b, n_st)

  (* build f<1> = el /\ f<2> = er *)
  let build_ref_deq st f el er =

    let unit_ty    = EB.mk_ty_unit st None                     in

    let (r_b, r_st)= ES.extend st "u" false true unit_ty       in

    let r_f        = exp_shift 0 1 f                           in
    let r_el       = exp_shift 0 1 el                          in
    let r_er       = exp_shift 0 1 er                          in

    (* EG: This is a common patter now, abstract it out *)
    let r_fl, r_fr = exp_project r_f                           in

    let eq_l       = EB.mk_exp_bin r_st EC.eq_op r_fl r_el     in
    let eq_r       = EB.mk_exp_bin r_st EC.eq_op r_fr r_er     in

    let ref_ass    = EB.mk_exp_bin r_st EC.l_and eq_l eq_r     in

    (* Build the constraint type *)
    let ref_ty     = EB.mk_ty_ref r_st r_b unit_ty ref_ass None in

    (* Safety check *)
    (* Disabled for now due to mutual definition issues        *)
    (* wf_type r_st ref_ty; *)

    let (n_b, n_st)= ES.extend st "ref_" false true ref_ty      in
    (n_b, n_st)

  (* Shortcut for symmetric case *)
  let build_nref_eq st f e =

    let el, er = exp_project e in
    build_ref_deq st f el er

  (* FIXME *)
  let rec occurs t ot = ()

  let rec check_subtype st (ty1 : ty) (ty2 : ty) : unit =

    let ty_err = new_error_st st @@ TypeMismatch(st, ty1, ty2) in

    (* Get types and possible refinement expression *)
    let ty1_e   = ty_e ty1 in

    let if_ty_e f ty =
      match ty1_e with
      | None   -> ty
      | Some e -> f e      in

    let ty_inject ty e =
      let loc = ty.L.pl_loc           in
      let ity = ty_u ty               in

      (* Synchronous case *)
      (match ty_e ty with
      | None    -> ()
      | Some e' -> ty_debug2 ty "!!! Replacing refinement hint @[@[%a@]@;: @[@[%a@]@;with @[%a@]@]@]"
        P.pp_ty ty P.pp_eann e' P.pp_eann e
      ) ;
      L.mk_loc loc @@ (ity, Some e)
    in

    let ty_propagate_ann ty ty_a =
      match ty_e ty_a with
      | None   -> ty
      | Some e -> ty_inject ty e
    in

    let ty1_u   = ty_u ty1 in
    let ty2_u   = ty_u ty2 in

    (* Check physical eq *)
    if ty1_u == ty2_u then () else begin
    (* Check structural eq *)
    if ty_eq ty1 ty2 then
      ty_debug3 ty1 "*** @[%a@] Subtyping equal types @[@[%a@]@;:<: @[%a@]@]" pp_tyst st P.pp_ty ty1 P.pp_ty ty2
    else begin
      ty_info2  ty1 "*** @[%a@] subtyping @[@[%a@] :<:@;@[%a@]@]" pp_tyst st P.pp_ty ty1 P.pp_ty ty2;
      match ty1_u, ty2_u with

    (* Follow links first *)
    | TVar {contents = TV_Link t1}, _ ->
      (* Propagate injection on references *)
      let t1 = ty_propagate_ann t1 ty1 in
      check_subtype st t1 ty2

    | _, TVar {contents = TV_Link t2} ->
      (* Propagate injection on references *)
      let t2 = ty_propagate_ann t2 ty2 in
      check_subtype st ty1 t2

    (* Simple unify *)
    | TVar ({contents = TV_Free _} as tv), _ ->
      (* ty_info ty2 "First is free, we unify to [%a]" P.pp_ty ty2; *)
      occurs tv ty2;
      (* XXXX: Remove the refinement in unification. Horrible hack. *)
      let unref ty = match ty_u ty with
        | TRef(_, ty, _) -> ty
        | _ -> ty in
      tv := TV_Link (unref ty2)

    | _, TVar ({contents = TV_Free _} as tv) ->
      (* ty_info ty2 "Second is free, we unify to [%a]" P.pp_ty ty1; *)
      occurs tv ty1;
      let unref ty = match ty_u ty with
        | TRef(_, ty, _) -> ty
        | _ -> ty in
      tv := TV_Link (unref ty1)

    (* Hack *)
    | TQVar v1, TQVar v2                     -> if v1 <> v2 then fail ty_err

    | TPrim(ty1, tyargs1), TPrim (ty2, tyargs2) ->
      if ty1 = ty2 && List.length tyargs1 = List.length tyargs2 then
        List.iter2 (fun t1 t2 -> check_subtype st t1 t2) tyargs1 tyargs2
      else
        fail ty_err

    (* FIXME: Do we want to do any fancy stuff here? *)
    | TC ty1, TC ty2 ->
      check_subtype st ty1 ty2

    | TM(a1, d1, ty1), TM(a2, d2, ty2) ->

      check_float_le st a1 a2;
      check_float_le st d1 d2;

      (* We could inject a lifting here to allow refinement over
         monadic types
      *)
      check_subtype st ty1 ty2

    | TPi(bi1, ty1_a, ty1_r), TPi(bi2, ty2_a, ty2_r) ->

      check_subtype st ty2_a ty1_a;

      let pi_st = ES.open_binder st bi2 ty2_a           in

      (* If the left type was coming from an expression, refine *)
      let ty1_r' = if_ty_e (fun (el, er) ->

        (* e is the expresssion of the functional type  *)
        let el_sh  = exp_shift 0 1 el                   in
        let er_sh  = exp_shift 0 1 er                   in
        let rl_var = EB.mk_exp_var pi_st 0 bi2          in
        let rr_var = EB.mk_exp_var pi_st 0 bi2          in

        (* We attach to ty1_r the expression "e x"      *)
        let rl_exp = EB.mk_exp_app pi_st el_sh [rl_var] in
        let rr_exp = EB.mk_exp_app pi_st er_sh [rr_var] in

        (* FIXME: This introduces eta-expanded terms    *)
        ty_inject ty1_r (rl_exp, rr_exp)
      ) ty1_r in

      check_subtype pi_st ty1_r' ty2_r

    (* XXX TODO: Merge the two cases, we should add the refinement
       information to fo1 if present
    *)
    | TRef(bi1, ty1, fo1), TRef(bi2, ty2, fo2)        ->

      check_subtype st ty1 ty2;

      (* We don't need to check refinements inside assertions  *)
      if not st.L.pl_desc.ES.in_assertion then

        (* Hack to update the location *)
        let ref_st = {st with L.pl_loc = fo2.L.pl_loc}    in
        let ref_st = ES.open_binder ref_st bi2 ty2        in
        check_implies ref_st fo1 fo2

    (* Main refinement case:
       - add a refinement to the context if ty1 had an expression annotation.
       - check that fo2 holds
    *)
    | _, TRef(bi2, ty2, fo2)                       ->

      (* First check that they are of the same base type *)
      check_subtype st ty1 ty2;

      (* We don't need to check refinements inside assertions  *)
      if not st.L.pl_desc.ES.in_assertion then

      (* Now build the refinement *)
      let ref_st = ES.open_binder st bi2 ty2                    in

      begin match ty1_e with
      | None          -> check_assertion ref_st fo2
      | Some (el, er) ->
        ty_info ty1 "!R! Trying refinement";

        (* Add "bi2   = e" to the context *)
        let ref_el    = exp_shift 0 1 el                        in
        let ref_el    = exp_project_side SiLeft  ref_el         in

        let ref_er    = exp_shift 0 1 er                        in
        let ref_er    = exp_project_side SiRight ref_er         in

        let vref      = EB.mk_from_id ref_st bi2.b_name         in

        let n_b, n_st = build_ref_deq ref_st vref ref_el ref_er in

        let n_fo      = exp_shift 0 1 fo2                       in

        check_assertion n_st n_fo
      end

    (* REVIEW this rule, but I think it should be straightfoward *)
    | TRef(_, ty1, fo1), _                            ->
      check_subtype st ty1 ty2

    | _                                               ->
      fail ty_err
    end
    end

  (* Check that the projections of e satisfy the predicate ity_skeleton *)
  let check_skeleton st ity e =
    let sk_pred  = ity ^ "_skeleton"                in
    let e_l, e_r = exp_project e                    in
    let ass      = EB.mk_exp_bin st sk_pred e_l e_r in
    check_assertion st ass

  (* Check that the type is a Pi type *)
  let rec check_app_shape ty =
    match ty_u ty with
    | TVar {contents = TV_Link ty} -> check_app_shape ty
    | TPi(b_ty, a_ty, r_ty) -> (b_ty, a_ty, r_ty)
    | TRef(b_ty, r_ty, _fo) -> check_app_shape r_ty
    | _                     -> fail (new_error ty @@ WrongShape(ty, "Functional"))

  (* FIXME: We should also check for refined C and M types... *)
  let rec check_m_shape ty =
    match ty_u ty with
    | TVar {contents = TV_Link ty} -> check_m_shape ty
    | TRef(b_ty, r_ty, _fo)        -> check_m_shape r_ty
    | TM(e_a, e_d, ty)             -> ty, e_a, e_d
    | _                            -> fail (new_error ty    @@ WrongShape(ty, "PMonadic"))

  let rec check_c_shape ty =
    match ty_u ty with
    | TVar {contents = TV_Link ty} -> check_c_shape ty
    | TC ty              -> ty
    | _                  -> fail (new_error ty    @@ WrongShape(ty, "CMonadic (let rec?)"))

  (* XXX: Clean up  *)
  let rec check_ty_ind_shape st (ty : ty) =
    match ty_u ty with
    | TVar {contents = TV_Link ty} -> check_ty_ind_shape st ty
    | TPrim(ty_n, ty_args) ->
      (* Missing laziness here *)
      begin
        match snd @@ ES.with_env st (fun e -> Env.lookup_type e (snd ty_n)) with
        | []             -> fail @@ new_error ty @@ WrongShape(ty, "an inductive")
        | ty_cons        -> (ty_n, ty_args, ty_cons)
      end
    | _         -> fail @@ new_error ty @@ WrongShape(ty, "an inductive")

end

open Subtyping

(**********************************************************************)
(* Main typing routines                                               *)
(**********************************************************************)

let type_of_const c : ty =
  match c with
  | ECInt  _ -> EC.ty_int
  | ECReal _ -> EC.ty_real

(*************************************************************************)
(* Instantiate free Q variables in a type                                *)

(* MOVED TO parsetree.ml *)

(*************************************************************************)
(* Simple constructor coverage checking *)
let check_cs_cov st cs_l cases =
  (* We build a set with the constructors, remove the current ones and
     check that the set is empty *)
  let cov_err pat cs = fail @@ new_error pat @@ WrongCoverage(cs)      in
  let cs_set     = StrSet.of_list @@ List.map snd cs_l                 in
  let cs_pats    = List.map fst cases                                  in

  let rec process_cons cs_set pat_l =
    match pat_l with
    (* No more cs obligations *)
    | [] -> if not (StrSet.is_empty cs_set) then
        cov_err st @@ List.hd @@ StrSet.elements cs_set
    | cs :: csl ->
      let cs_n = snd @@ fst @@ L.unloc cs in
      if not (StrSet.mem cs_n cs_set) then
        cov_err cs cs_n
      else
        let n_set = StrSet.remove cs_n cs_set in
        process_cons n_set csl
  in
  process_cons cs_set cs_pats

let rec type_of e_st e : ty =
  (* E.exp_sanity e_st e; *)
  let e_st     = L.uloc e_st e.L.pl_loc         in

  ty_debug  e "--> @[%a@] Enter type_of: @[%10a@]" pp_tyst e_st (P.limit_boxes P.pp_exp) e; 
  ty_debug2 e "--> @[%a@]" P.pp_env (ho_env e_st);
  incr ty_seq;

  (* FIXME: We miss some potentially useful injections *)
  let ty_inj       ty = L.mk_loc (L.getloc e_st) @@ (ty, Some (e, e))       in
  let ty_inj_exp e ty = L.mk_loc e.L.pl_loc (fst ty.L.pl_desc, Some (e, e)) in

  let ty = match L.unloc e with
    | EConst c          -> ty_inj_exp e @@ type_of_const c

    | EImport (th, e) ->
      let i_st = ES.update_env e_st (WhyImport.load_why3_theory th) in
      type_of i_st e

    | EPrim p           ->
      ty_inj_exp e @@ ty_instantiate @@ ES.prim_type e_st (snd p)


(* ty_inj_exp e @@ E.ity_to_ty e_st @@ Ity.ity_instantiate_list @@ ES.prim_type e_st (snd p) *)

    (*******************************************************************)
    (* Var                                                             *)
    (*******************************************************************)


    | EVar v            -> let (bi, ty)  = ES.access e_st v.v_index                    in
                           let ty        = ty_inj_exp e ty                             in

                           (* FIXME: Polymorphism is a hack *)
                           (* begin match ty_u ty with *)
                           (* | TVar tv -> ty_info ty "Init EVar: @[%a@]@@(%x)" P.pp_tvar !tv (2 * (Obj.magic tv)) *)
                           (* | _ -> () *)
                           (* end; *)
                           let ty        = ty_instantiate ty                           in
                           (* begin match ty_u ty with *)
                           (* | TVar tv -> ty_info ty "End EVar: @[%a@]@@(%x)" P.pp_tvar !tv (2 * (Obj.magic tv)) *)
                           (* | _ -> () *)
                           (* end; *)

                           let check c r = iwhen c r @@ new_error e @@ WrongBinding e  in

                           if not e_st.L.pl_desc.ES.in_assertion then
			     check (v.v_side = SiNone) ty
			   else
			     (* We are in an assertion, depending on the
			        binding mode we have one addressing mode or
			        another. *)
			     if bi.b_rel then
			       check (v.v_side = SiLeft || v.v_side = SiRight) ty
			     else
			       check (v.v_side = SiNone) ty

    | ELam(bi, ty, e1) ->

      (* Check annotation *)
      wf_type e_st ty;

      (* FIXME: Polymorphism is a hack *)
      (* let ty    = ty_instantiate ty               in *)

      let e1_st = ES.open_binder e_st bi ty       in
      let e1_ty = type_of e1_st e1                in

      ty_inj @@ TPi(bi, ty, e1_ty)

    (*******************************************************************)
    (* App                                                             *)
    (*******************************************************************)

    (* The rule implemented here subsumes subtyping as standard:

       Γ ⊢ e₁ : Π (x :: T). U     Γ ⊢ e₂ : T'  Γ ⊢ T' <: T
       ───────────────────────────────────────────────────
       Γ ⊢ e₁ e₂ : U[x/e₂]

    *)
    | EApp(e_f, e_l)    ->

      (* Check a single application *)
      let type_of_bin_app st f_ty e_arg =

        let (b_ty, a_ty, r_ty) = check_app_shape f_ty     in

        let arg_ty             = type_of st e_arg         in

        (* Inject e_arg into arg_ty *)
        let arg_ty = ty_inj_exp e_arg arg_ty              in
        check_subtype st arg_ty a_ty;

	ty_subst 0 e_arg r_ty
      in

      let rec type_of_list_app st f_ty e_l = match e_l with
        | []            -> f_ty
        | e_arg :: rest ->
          let ty_app = type_of_bin_app st f_ty e_arg      in
          type_of_list_app st ty_app rest
      in

      (* Type the function *)
      let f_ty              = type_of e_st e_f            in

      (* Now type the argument list *)
      let ty_app = type_of_list_app e_st f_ty e_l         in

      (* Inject the full expression *)
      ty_inj_exp e ty_app

    (*******************************************************************)
    (* Let                                                             *)
    (*******************************************************************)

    (* The rule implemented here is a variation of app:

       Γ ⊢ e₁ : T'     Γ, x ∷ T ⊢ e₂ : U     T' <: T
       ───────────────────────────────────────────────
       Γ ⊢ let (x ∷ T) = e₁ in e₂ : U[x/e₁]

       TODO: Check again the behaviour of annotations
    *)

    | ELet(bi, tr, ty_ann, e1, e2) ->

      (* The annotation must be well-typed *)
      wf_type e_st ty_ann;

      (* FIXME: prop checks? *)
      (* wf_type st ty (if p then enable_prop opts else disable_prop opts); *)

      let e1_ty = begin
        let e1_ty = type_of e_st e1                  in

        let let_st =
          match tr with
          | None         -> e_st
          | Some vc_name -> ty_warning e "!T! Trusting @[%a@] (%s) of type @[%a@]" P.pp_binfo bi vc_name P.pp_ty ty_ann;
                            ES.enable_trust vc_name e_st
        in
        (* FIXME: Still not fine if we generate more than one VC for a trust *)
        check_subtype let_st e1_ty ty_ann;
        ty_inj_exp e1 ty_ann
      end
      in

      (* Type e2 *)
      let e2_st = ES.open_binder e_st bi e1_ty       in
      let e2_ty = type_of e2_st e2                   in

      (* ty_info e "Substituting %a in @[%a@] by @[%a@]" P.pp_binfo bi P.pp_ty e2_ty P.pp_exp e1; *)
      ty_subst 0 e1 e2_ty

    (*******************************************************************)
    (* Fix                                                             *)
    (*******************************************************************)

    (* FIXME: Update rule below *)
    (* The rule is similar to let but we don't substitute in the
       return type for now:

       Γ, f ∷ T, x ∷ U ⊢ e₁ : T'     Γ ⊢ T' <: T
       Γ, f ∷ T. U     ⊢ e₂ : V
       ───────────────────────────────────────────────
       Γ ⊢ fix (f x ∷ Pi x :: T. U) = e₁ in e₂ : V

    *)

    | EFix(bi, ty, tc, e) ->

      wf_type e_st ty;

      (* We introduce the fixpoint term. *)
      let fix_st         = ES.open_binder e_st bi ty   in

      let e_ty = type_of fix_st e in

      begin
        match tc with
        (* FIXME: Add termination check *)
        | Some ta  -> if not (TermCheck.check e_st e ta) then
            fail @@ new_error e @@ Termination e
        | None     ->
          let co_ty = ty_codomain e_ty    in
          let _     = check_c_shape co_ty in
          ()
      end;

      (* FIXME: Occurs check *)
      let e_ty_u = ty_shift 0 (-1) e_ty in
      check_subtype e_st e_ty_u ty;

      (* We return the annotation *)
      ty                                (* Inject? *)

    (*******************************************************************)
    (* Constructor                                                     *)
    (*******************************************************************)

    | ECs c ->
      begin
        try (* Enable refinement for constructors *)
          ty_inj_exp e @@ ty_instantiate @@ ES.cons_type e_st (snd c)
        with Not_found -> fail @@ new_error e @@ MissingIdent (snd c)
      end

    (*******************************************************************)
    (* Synchronous Match                                               *)
    (*******************************************************************)
    (* Match ...

       Γ ⊢ L ∶ { L ∷ List A | ϕ ∧ skeleton(L<1>, L<2>) }

       Γ,                    _ ∷ { _ ∷ unit | ϕ [nil/x]       ∧ L = nil       } ⊢ M : Bₗ
       Γ,                    _ ∷ { _ ∷ unit | ϕ [nil/x]       ∧ L = nil       } ⊢ Bₗ <: B

       Γ, a ∷ A, l ∷ list A, _ ∷ { _ ∷ unit | ϕ [cons(a,l)/x] ∧ L = cons(a,l) } ⊢ N : Bᵣ
       Γ, a ∷ A, l ∷ list A, _ ∷ { _ ∷ unit | ϕ [cons(a,l)/x] ∧ L = cons(a,l) } ⊢ Bᵣ <: B
       ──────────────────────────────────────────────────────────────────────────────────
       match L with[B] nil -> M | cons(a, l) -> N : B

    *)

    | EMatch (false, e_m, cases, ret_ty) ->

      (* Prepare for bidirectional TC *)
      let ret_ty = match ret_ty with
        | None    -> fail (new_error e @@ CannotInfer(e))
        | Some ty -> ty
      in

      (* Typing for branches *)
      let type_of_branch b_st b_pat b_e ty_m b_ty  =

        let (p_cons, p_bind) = L.unloc b_pat in
        let cs_name = snd p_cons             in

        (* Check arity of the pattern *)
        let n_binding      = List.length p_bind                        in
        let (cs_th, cs_ty) = Env.lookup_cons (ES.getenv b_st) cs_name  in
        let cs_arity       = function_arity cs_ty                      in

        if n_binding <> cs_arity then
          fail (new_error b_pat @@ WrongPattern(cs_name, cs_arity) )
        ;

        (* Instantiate types of the constructors *)
        let cs_ty = ty_instantiate cs_ty in

        (* Introduce bindings *)
        let rec introduce_pat st bi_l ty_l = begin
          match bi_l, ty_u ty_l with
          | [], _                        -> st
          | bi :: bi_l, TPi(_, ty, ty_l) ->
            let b_st = ES.open_binder st bi @@ ty in
            (* let b_st = ES.open_binder st bi (L.mk_loc b_pat.pl_loc @@ ity_to_ty st ty, None) in *)
            introduce_pat b_st bi_l ty_l
          | _ -> typing_error e "Internal error in introduce_pat @[%a@]" P.pp_exp e
        end in

        let b_e_st = introduce_pat b_st p_bind cs_ty                in

        (* Introduce the refinement {() :: e_m = p_cons b_1 ... b_m) *)
        let rec e_binder n b_l = match b_l with
          | []      -> []
          | b :: bl -> EB.mk_exp_var b_e_st n b ::
            e_binder (n - 1) bl                              in
        let e_pat    = EB.mk_app_list (EB.mk_exp_cs b_e_st p_cons) @@
          e_binder (List.length p_bind - 1) p_bind in

        (* The pattern must be well-typed *)
        let ty_pat     = type_of b_e_st e_pat                           in
        let ty_m_shift = ty_shift 0 n_binding ty_m                      in

        (* EG: We compare only the skeletons here. *)
        (* Note that we could try to be smarter and detect
           non-reachable patterns.
        *)
        check_subtype b_e_st ty_pat (ty_skel ty_m_shift);

        (* We must also shift the original exp *)
        let e_m_shift     = exp_shift 0 n_binding e_m                   in
        let (_bc, bra_st) = build_nref_eq b_e_st e_m_shift e_pat        in

        (* Type the branch *)
        let b_e_sh = exp_shift 0 1 b_e     in
        let ty_b_e = type_of bra_st b_e_sh in

        (* Check that the returned type is an instance of the annotation  *)
        (* We need to shift it by the number of binders plus one for the ref *)
        let b_ty_sh = ty_shift 0 (n_binding + 1) b_ty in
        check_subtype bra_st ty_b_e b_ty_sh

      in

      (* Check the annotation *)
      wf_type e_st ret_ty;

      (* Type of the discriminee *)
      let ty_m = type_of e_st e_m in

      (* EG: This test is redundant now, as we only allow constructors
         to start a pattern, and later we will type the pattern, so it
         is not possible to match a non-inductive; but it may be
         needed in the future *)

      (* Check that ty_m is a valid IType *)
      let ty_m_sk         = ty_skel ty_m                    in
      let (ty_n, _, cs_l) = check_ty_ind_shape e_st ty_m_sk in

      (* Check constructor coverage for ty_m *)
      check_cs_cov e_st cs_l cases;

      (* Check skeleton *)
      check_skeleton e_st (snd ty_n) e_m;

      (* Check branches *)
      List.iter (fun (b_pat, b_e) ->
        type_of_branch e_st b_pat b_e ty_m ret_ty) cases;

      (* Return the annotation *)
      ret_ty

    (*******************************************************************)
    (* Asynchronous Match                                              *)
    (*******************************************************************)

    | EMatch (true, e_m, cases, ret_ty) ->

      (* Prepare for bidirectional TC *)
      let ret_ty = match ret_ty with
        | None    -> fail (new_error e @@ CannotInfer(e))
        | Some ty -> ty
      in

      (* Call the async typer, use bidirectional type checking *)
      rtype_of e_st e e ret_ty

    (*******************************************************************)
    (* DUnit/DLet                                                      *)
    (*******************************************************************)
    | EMUnit (DMonad _, e_u)                                             ->
      typing_error e_st "dunit not implemented"

    | EMLet(DMonad _, b1, ty_a, e1, e2)                                  ->
      typing_error e_st "dlet not implemented"

    (*******************************************************************)
    (* MUnit                                                           *)
    (*******************************************************************)

    (*

      Γ ⊢ e_u : T
      ──────────────────────────
      Γ ⊢ munit e_u : M [1, 0] T

    *)

    (* e = munit e_u *)
    | EMUnit (PMonad, e_u)                                                ->

      let e_ty  = type_of e_st e_u                                        in
      (* Remove annotation *)
      let e_ty  = erase_ty_ann e_ty                                       in
      let alpha = EB.mk_exp_float e_st 0.0                                in
      let delta = EB.mk_exp_float e_st 0.0                                in

      EB.mk_ty_m e_st alpha delta e_ty None

    (*******************************************************************)
    (* MLet                                                            *)
    (*******************************************************************)

    (*
      Γ         ⊢ (α₀, δ₀) : (ℝ × ℝ)      Γ        ⊢ P : M_[α₁, δ₁] T
      Γ, x :: T ⊢ (α₁, δ₁) : (ℝ × ℝ)      Γ, x : T ⊢ Q : M_[α₂, δ₂] U
      ───────────────────────────────────────────────────────────────────────────────────────
      Γ ⊢ mlet x = P in Q : M [α₁*α₂, δ₁+δ₂] U [x ← P]
    *)

    | EMLet(PMonad, b1, ty_a, e1, e2)                                     ->

      Option.may (wf_type e_st) ty_a;

      (* Type check e1                                                    *)
      let e1_ty              = type_of e_st e1                            in
      let e1_mty, e1_a, e1_d = check_m_shape e1_ty                        in

      (* Type check e2                                                    *)
      let e2_st              = ES.open_binder e_st b1 e1_mty              in
      let e2_ty              = type_of e2_st e2                           in
      let e2_mty, e2_a, e2_d = check_m_shape e2_ty                        in

      (* Note that we allow the typechecking to proceed, however, x
         must not occur free in ret_ty

         For now we check that it is not the case, otherwise we bail
         out.

         We could support an annotation here or use bidirectional type
         checking, still thinking about what is the best approach.
      *)

      (* If we have an annotation then we can check the full type *)
      begin match ty_a with
      | None ->
        (* We must check that the inferred type is well formed. *)
        let e2_mty_fv = ty_free_vars  e2_mty                                in
        let e2_a_fv   = exp_free_vars e2_a                                  in
        let e2_d_fv   = exp_free_vars e2_d                                  in
        let e2_fv     = union_list_iset [e2_mty_fv; e2_a_fv; e2_d_fv]       in

        if IntSet.mem 0 e2_fv then
          typing_error e "Bound variable @[%a@] not free in mlet type: @[%a@]!" P.pp_binfo b1 P.pp_ty e2_ty;
        (* else, we can safely eliminate the variable *)

        let e2_mty    = ty_subst  0 e1 e2_mty                               in
        let e2_a      = exp_subst 0 e1 e2_a                                 in
        let e2_d      = exp_subst 0 e1 e2_d                                 in

        (* FIXME: what about the types of e2_a, should we check them? *)
        let ret_a  = EB.mk_exp_bin e_st EC.add_float e1_a e2_a              in
        let ret_d  = EB.mk_exp_bin e_st EC.add_float e1_d e2_d              in

        (* We now build the return type *)
        EB.mk_ty_m e_st ret_a ret_d e2_mty None

      | Some ty ->
        (* However, now we must perform a subtyping check against the
           annotation, shifting is in order *)
        let e1_a   = exp_shift 0 1 e1_a                                     in
        let e1_d   = exp_shift 0 1 e1_d                                     in
        let ret_a  = EB.mk_exp_bin e2_st EC.add_float e1_a e2_a             in
        let ret_d  = EB.mk_exp_bin e2_st EC.add_float e1_d e2_d             in
        let in_ty  = EB.mk_ty_m e2_st ret_a ret_d e2_mty None               in

        (* We now do the check *)
        let ty_sh = ty_shift 0 1 ty in
        check_subtype e2_st in_ty ty_sh;

        (* Return the annotation *)
        ty
      end

    (*******************************************************************)
    (* CUnit                                                           *)
    (*******************************************************************)

    | EMUnit(CMonad, e_u)                                                ->
      let e_ty = type_of e_st e_u in

      (* Remove annotation *)
      let e_ty  = erase_ty_ann e_ty                                       in
      EB.mk_ty_c e_st e_ty None

    (*******************************************************************)
    (* CLet                                                            *)
    (*******************************************************************)

    | EMLet(CMonad, b1, ty_a, e1, e2)                                     ->

      Option.may (wf_type e_st) ty_a;

      (* Type check e1                                                    *)
      let e1_ty              = type_of e_st e1                            in
      let e1_cty             = check_c_shape e1_ty                        in

      (* Type check e2                                                    *)
      let e2_st              = ES.open_binder e_st b1 e1_cty              in
      let e2_ty              = type_of e2_st e2                           in
      let e2_cty             = check_c_shape e2_ty                        in

      (* Note that we allow the typechecking to proceed, however, x
         must not occur free in ret_ty

         For now we check that it is not the case, otherwise we bail
         out.

         We could support an annotation here or use bidirectional type
         checking, still thinking about what is the best approach.
      *)

      (* If we have an annotation then we can check the full type *)
      begin match ty_a with
      | None ->
        (* We must check that the inferred type is well formed. *)
        let e2_fv = ty_free_vars  e2_cty                                in

        if IntSet.mem 0 e2_fv then
          typing_error e "Bound variable @[%a@] not free in clet type: @[%a@]!" P.pp_binfo b1 P.pp_ty e2_ty;
        (* else, we can safely eliminate the variable *)

        let e2_cty    = ty_subst  0 e1 e2_cty                               in

        (* We now build the return type *)
        EB.mk_ty_c e_st e2_cty None

      | Some ty ->
        (* We have an annotation, perform a subtyping check against
           it, shifting is in order *)

        let in_ty  = EB.mk_ty_c e2_st e2_cty None               in

        let ty_sh = ty_shift 0 1 ty in
        check_subtype e2_st in_ty ty_sh;

        (* Return the annotation *)
        ty
      end

  (**********************************************************************)
  in
  decr ty_seq;
  (* Limit pp_term *)
  ty_debug  e "<-- @[%a@] Exit  type_of: @[%a@] @\n          with type    : @[%a@]" pp_tyst e_st (P.limit_boxes P.pp_exp) e P.pp_ty ty;
  (* We never modify the output environment (for now) *)
  ty_debug3 e "<-- @[%a@]" P.pp_env (ho_env e_st);
  ty

and rtype_of e_st e1 e2 (goal_ty : ty) =
  (* E.exp_sanity e_st e; *)
  let e_st     = L.uloc e_st e1.L.pl_loc         in

  ty_debug  e_st "--> [%3d] Enter rtype_of: @[%a@] ~ @[%10a@]" !ty_seq (P.limit_boxes P.pp_exp) e1 (P.limit_boxes P.pp_exp) e2;
  ty_debug2 e_st "--> @[%a@]" P.pp_env (ho_env e_st);
  incr ty_seq;

  (* Asynchronous typing.

     For now we apply a very basic heuristic, if e1 is a match we
     proceed, otherwise, if e2 is a match we apply symmetry, othewise,
     we try to apply non-relational typing or we fail.

     We will improve as examples demand it.
  *)
  let ty = match L.unloc e1, L.unloc e2 with

    | EMatch (_, e1_m, br1, ret_ty1), _ ->

      (* Prepare for bidirectional TC *)
      let ret_ty1 = begin
        match ret_ty1 with
        | None    -> fail (new_error e1 @@ CannotInfer(e1))
        | Some ty -> ty
      end in

      (* Apply the async match rule *)
      let rtype_of_branch b_st b_pat b_e ty_m b_ty =

        let (p_cons, p_bind) = L.unloc b_pat in
        let cs_name = snd p_cons             in

        (* Check arity of the pattern *)
        let n_binding      = List.length p_bind                        in
        let (cs_th, cs_ty) = Env.lookup_cons (ES.getenv b_st) cs_name  in
        let cs_arity       = function_arity cs_ty                      in

        if n_binding <> cs_arity then
          fail (new_error b_pat @@ WrongPattern(cs_name, cs_arity) )
        ;

        (* Instantiate types of the constructors *)
        (* XXX: FIXME Ity removal *)
        (* let cs_ty = Ity.ity_instantiate_list cs_ty in *)

        (* Introduce bindings *)
        let rec introduce_pat st bi_l ty_l = begin
          match bi_l, ty_u ty_l with
          | [], _                   -> st
          | bi :: bi_l, TPi (_, ty, ty_l)  ->
            let b_st = ES.open_binder st bi ty in
            (* let b_st = ES.open_binder st bi (L.mk_loc b_pat.pl_loc @@ ity_to_ty st ty, None) in *)
            introduce_pat b_st bi_l ty_l
          | _ -> typing_error b_st "Internal error in introduce_pat @[%a@]" P.pp_exp e1
        end in

        let b_e_st = introduce_pat b_st p_bind cs_ty                 in

        (* Introduce the refinement {() :: e_m = p_cons b_1 ... b_m) *)
        let rec e_binder n b_l = match b_l with
          | []      -> []
          | b :: bl -> EB.mk_exp_var b_e_st n b ::
            e_binder (n - 1) bl                                      in

        let e_pat    = EB.mk_app_list (EB.mk_exp_cs b_e_st p_cons) @@
          e_binder (List.length p_bind - 1) p_bind                   in

        (* The pattern must be well-typed *)
        let ty_pat     = supress (fun () -> type_of b_e_st e_pat)    in
        let ty_m_shift = ty_shift 0 n_binding ty_m                   in

        (* EG: We compare at the PCF type level here. *)
        (* We could try to be smarter and detect non-reachable
           patterns, etc...  *)
        supress (fun () ->
          check_subtype b_e_st ty_pat (ty_skel ty_m_shift)
        );

        (* We must also shift the original exp *)
        let e_m_shift     = exp_shift 0 n_binding e1_m               in

        let e_m_l         = exp_project_side SiLeft e_m_shift        in
        let e_pat_l       = exp_project_side SiLeft e_pat            in
        let (_bc, bra_st) = build_ref_eq b_e_st e_m_l e_pat_l        in

        (* Type the branch asynchronously *)
        let b_e_sh = exp_shift 0 1 b_e                               in

        (* We must also shift e2 for the refinement! *)
        let e2_sh  = exp_shift 0 1 e2                                in

        let b_ty_sh = ty_shift 0 (n_binding + 1) b_ty                in

        (* Push the goal_ty *)
        let ty_b_e = rtype_of bra_st b_e_sh e2_sh b_ty_sh            in

        (* Check that the returned type is an instance of the annotation  *)
        (* We need to shift it by the number of binders plus one for the ref *)
        check_subtype bra_st ty_b_e b_ty_sh

      in

      (* Check the annotation *)
      supress (fun () ->
        wf_type e_st ret_ty1
      );

      (* Type of the discriminee *)
      let ty_m1 = supress (fun () -> type_of e_st e1_m) in

      (* Check that ty_m is a valid IType *)
      let ty_m1_sk         = ty_skel ty_m1                    in
      let _cs, _args, cs_l = check_ty_ind_shape e_st ty_m1_sk in

      (* Check constructor coverage for ty_m *)
      check_cs_cov e_st cs_l br1;

      (* Check branches *)
      List.iter (fun (b_pat, b_e) ->
        rtype_of_branch e_st b_pat b_e ty_m1 ret_ty1) br1;

      (* Return the annotation *)
      ret_ty1

    | _, EMatch _ ->

      (* Apply the symmetry rule *)
      let swap_st      = ES.update_env e_st Env.swap_side         in
      let swap_e1      = exp_swap e1                              in
      let swap_e2      = exp_swap e2                              in
      let swap_goal_ty = ty_swap goal_ty                          in

      let swap_ty = rtype_of swap_st swap_e2 swap_e1 swap_goal_ty in
      ty_swap swap_ty

    (* We cannot reach this point with two matches, otherwise we would loop. *)

    (* FIXME: We just try the refinement base rule and don't do anything fancy here. *)
    | _ ->
      (* We call the sync typer here but replace the annotations *)
      let e1_ty = type_of e_st e1 in
      let e2_ty = type_of e_st e2 in

      let n_ann = (e1, e2)        in

      let e1_ty = modify_ty_ann e1_ty n_ann in
      let e2_ty = modify_ty_ann e2_ty n_ann in

      check_subtype e_st e1_ty goal_ty;
      check_subtype e_st e2_ty goal_ty;

      goal_ty
  in
  decr ty_seq;
  (* Limit pp_term *)
  ty_debug  e_st "<-- [%3d] Exit  rtype_of: @[%a@] ~ @[%a@] @\n          with type    : @[%a@]" !ty_seq (P.limit_boxes P.pp_exp) e1 (P.limit_boxes P.pp_exp) e2 P.pp_ty ty;
  (* We never modify the output environment (for now) *)
  ty_debug3 e_st "<-- @[%a@]" P.pp_env (ho_env e_st);
  ty

and wf_ann an_st ty_a =
  let (ty, p) = ty_a                          in
  wf_type an_st ty

and wf_type ty_st ty = match ty_u ty with

  | TVar {contents = TV_Free _}  -> ()
  | TVar {contents = TV_Link ty} -> wf_type ty_st ty
  | TQVar                      _ -> ()

  | TPrim(_tc, ty_args)          ->
    List.iter (wf_type ty_st) ty_args

  | TC   ty                      ->
    wf_type ty_st ty

  | TG   (mty, e_d, ty_m)        ->

    let check_type_m_float st e =
      let ty_e = type_of st e in
      check_subtype st ty_e (EB.mk_ty_float st)
    in

    (* We are in assertion mode for α, δ *)
    let m_st = ES.enable_ass ty_st in

    ty_info2 m_st "s-> Entering the simply typed world!";

    check_type_m_float m_st e_d;

    ty_info2 m_st "s<- Exiting the simply typed world!";

    wf_type ty_st ty_m

  | TM   (e_a, e_d, ty_m)        ->

    let check_type_m_float st e =
      let ty_e = type_of st e in
      check_subtype st ty_e (EB.mk_ty_float st)
    in

    (* We are in assertion mode for α, δ *)
    let m_st = ES.enable_ass ty_st in

    ty_info2 m_st "s-> Entering the simply typed world!";

    check_type_m_float m_st e_a;
    check_type_m_float m_st e_d;

    ty_info2 m_st "s<- Exiting the simply typed world!";

    wf_type ty_st ty_m

  | TPi  (bi, ty1, ty2)          ->
    wf_type ty_st ty1;

    let t1_st = ES.open_binder ty_st bi ty1                   in
    wf_type t1_st ty2

  | TRef (bi, ty_r, e_r)         ->

    wf_type ty_st ty_r;

    let as_st = ES.open_binder ty_st bi ty_r                  in

    let as_st = ES.enable_ass as_st                           in
    ty_info2 as_st "s-> Entering the simply typed world!";
    let as_ty = type_of as_st e_r                             in
    ty_info2 as_st "s<- Exiting the simply typed world!";
    iwhen ((ty_u as_ty) = EC.typ_prop) () (new_error as_ty @@ WrongAssertion(as_ty))

(* and wf_assertion fo env = match L.unloc fo with *)
(*   | FUnOp  (op, fo)              -> wf_assertion fo env *)

(*   | FBinOp (op, f1, f2)          -> *)
(*     wf_assertion f1 env; *)
(*     wf_assertion f2 env *)

(*   | FQuant (qf, bi, ty, fo)      -> *)
(*     let env_q = Env.extend_bi bi ty env in *)
(*     wf_assertion fo env_q *)

(*   (\* Key rule *\) *)
(*   | FPred  (p, e1, e2)           -> *)
(*     let t1 = type_of e1 env in *)
(*     let t2 = type_of e2 env in *)

(*     (\* Bam! *\) *)
(*     (\* Fixme: We are missing refinement here *\) *)
(*     iwhen (is_subtype t1 t2 || is_subtype t2 t1) () (new_error e1 @@ WrongAssertion(t1, t2)) *)

open Format
open Print

let pp_tyerr ppf s = match s with
  | TypeMismatch(st, ty1, ty2) -> fprintf ppf "EEE [%3d] @[Cannot subtype @[@[%a@] to@;@[%a@]@] in env:@\n@[%a@]@]" !ty_seq pp_ty ty1 pp_ty ty2 pp_env (ho_env st)
  | CannotApply(ty1, ty2)      -> fprintf ppf "EEE [%3d] Cannot apply %a to %a"                                     !ty_seq pp_ty ty1 pp_ty ty2
  | MissingIdent s             -> fprintf ppf "EEE [%3d] Primitive or constructor %s not found"                     !ty_seq s
  | CannotInfer e              -> fprintf ppf "EEE [%3d] Cannot Infer Type for @[%a@]"                              !ty_seq pp_exp e
  | WrongShape(ty, sh)         -> fprintf ppf "EEE [%3d] Type %a has wrong shape, expected %s type"                 !ty_seq pp_ty ty sh
  | WrongPattern(cs, n)        -> fprintf ppf "EEE [%3d] Pattern %s has wrong number of arguments, expected %d"     !ty_seq cs n
  | WrongCoverage(cs)          -> fprintf ppf "EEE [%3d] Coverage problem in pattern matching, constructor %s"      !ty_seq cs
  | WrongBinding e             -> fprintf ppf "EEE [%3d] Binding mode doesn't match address mode in variable %a"    !ty_seq pp_exp e
  | WrongAssertion(ty)         -> fprintf ppf "EEE [%3d] Assertion must of type Prop but is %a"                     !ty_seq pp_ty ty
  | AssertionFail(st, fo)      -> fprintf ppf "EEE [%3d] Couldn't prove @[%a@]@\nin env: @[%a@]"                    !ty_seq pp_exp fo pp_env (ho_env st)
  | Termination(e)             -> fprintf ppf "EEE [%3d] Termination check on:@\n @[%a@] failed."                   !ty_seq pp_exp e
  | PropDisabled               -> fprintf ppf "EEE [%3d] Prop is disabled for programs"                             !ty_seq

let loci loc = L.mk_loc loc ()

let get_type name (program : exp) : ty =
  try
    type_of (ES.initial name) program
  with TypeError e ->
    typing_error_pp e pp_tyerr (L.unloc e)
  | ParseError(loc, msg) ->
    error_msg Opts.TypeChecker program "%s" (EcUtils.odfl "Unknown error" msg)
