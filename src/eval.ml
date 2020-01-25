(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Parsetree
open EC.EcLocation

module E    = Exp
module ES   = E.ExpState
module P    = Print

(* Evaluator for open expressions to strong NF *)

open Support.Error
module Opts = Support.Options

let ev_error   fi   = error_msg Opts.SMT fi
let ev_warning fi   = message 1 Opts.SMT fi
let ev_info    fi   = message 2 Opts.SMT fi
let ev_info2   fi   = message 3 Opts.SMT fi
let ev_debug   fi   = message 4 Opts.SMT fi
let ev_debug2  fi   = message 5 Opts.SMT fi
let ev_debug3  fi   = message 6 Opts.SMT fi

(* We need closures if we aim to be reasonably modular *)
let cl ev = fun () -> ev

(* For evaluating open terms, we ask to the environment whether it
   knows of an expression for the variable (hack: using the env as a
   stack.

   If the variable has no associated expression, that means the
   variable is not bound and will be considered abstract in the VC
*)

let pick_side side (e_l, e_r) = match side with
  | SiNone  -> e_l
  | SiLeft  -> exp_project_side side e_l
  | SiRight -> exp_project_side side e_r

let access_var_exp st v = let env     = ES.getenv st             in
		          let (bi, ty) = Env.access env v.v_index in
                          (* Must project! *)
                          (* This is hacky *)
                          if bi.b_opaque then None
                          else
                            Option.map (
                              fun e ->
                                pick_side v.v_side e
                            ) @@ ty_e ty

let is_var_bound   st v =
  match access_var_exp st v with
  | None    -> false
  | Some _e -> true

(* If e can do a step then f, else r *)
let rec etry st e f r = match step st e with
  | None    -> r ()
  | Some e' -> Some (f e')

and etry_list st l f r = match l with
  | []       -> r ()
  | e :: e_r -> etry st e (fun e -> f (e :: e_r)) @@ cl @@
                                                     etry_list st e_r (fun l -> f (e :: l)) r

and step e_st e =
  (* ev_debug2 e "@[Step for @[%a@]" P.pp_exp e; *)

  let e_loc = e.pl_loc        in
  let reloc = mk_loc e_loc    in

  let res = match unloc e with
  | EImport _                    -> None
  | EPrim _s                     -> None
  | EConst _c                    -> None
  | EVar v                       -> access_var_exp e_st v

  | ELam (bi, ty, e_l)             ->
    let l_st = ES.open_binder e_st bi ty in
    etry l_st e_l (fun e -> reloc @@ ELam (bi, ty, e)) @@ cl None

  | EApp (e_f, [])               -> Some e_f
  | EApp (e_f, e_l) ->
    begin
      match unloc e_f with
      | ELam (_b, _t, e)  -> Some (reloc @@ EApp (exp_subst 0 (List.hd e_l) e, List.tl e_l))
      | _                 ->
         etry      e_st e_f (fun e -> reloc @@ EApp(e,   e_l)) @@
     cl (etry_list e_st e_l (fun e -> reloc @@ EApp(e_f, e))   @@
                                 cl None)
    end

  | ELet (bi, tr, ty, e1, e2)        ->
    etry e_st e1 (fun e1 -> reloc @@ ELet(bi, tr, ty, e1, e2))    @@
                 cl (Some (exp_subst 0 e1 e2))

  (* FIXME: Careful here, this is not really supported for now *)
  | EFix (bi, ty, tc, e) ->
    etry e_st e (fun e -> reloc @@ EFix(bi, ty, tc, e)) @@
                cl None
                  (* cl (Some (exp_subst 0 e1 e2)) *)

  | EMUnit (mt, e)                     ->
    etry e_st e (fun e -> reloc @@ EMUnit(mt, e)) @@ cl None

  (* FIXME: This was wrong! Disabled for now! *)
  | EMLet (mt, bi, ty_a, e1, e2) ->
    etry e_st e1 (fun e1 -> reloc @@ EMLet (mt, bi, ty_a, e1, e2)) @@
                cl None
              (* cl (Some (exp_subst 0 e1 e2)) *)

  | ECs _s ->
    None

  | EMatch (asy, e_m, pats, ty) ->
    (* Eval the constructor *)
    etry e_st e_m (fun e_m -> reloc @@ EMatch (asy, e_m, pats, ty)) @@
      (* If in NF,  *)
      cl @@ pat_subst e_m pats
  in
  (* ev_debug2 e "<-- Step for    @[%a@]" P.pp_exp e; *)
  (* ev_debug2 e "<-- Step result @[%a@]" (P.pp_option P.pp_exp) res; *)
  res
and pat_subst cons pats =
  (* Lets see if the argument to the match is a constructor *)
  let rec uncurry_cons e = match unloc e with
    | EApp (e1, e2) ->
      begin
        match uncurry_cons e1 with
        | Some (cs, l) -> Some (cs, l @ e2)
        | None         -> None
      end
    | ECs cs        -> Some (cs, [])
    | _             -> ev_debug3 e "Cannot reduce a non-constructor in a match! @[%a@]" P.pp_exp e;
                       None
  in
  match uncurry_cons cons with
  | None            -> None
  | Some (cs, args) -> Some(
    (* Extract the constructor of the pattern *)
    let p_list     = List.map (fun (pat, e) -> (fst (unloc pat), e)) pats in
    let exp        = List.assoc cs p_list                                 in
    (* Reverse the arguments *)
    let r_args     = List.rev args                                        in
    List.fold_left (fun e arg -> exp_subst 0 arg e) exp r_args)

(* Perform steps *)
let rec nstep e_st n s =
  if n = 0 then s
  else
    match step e_st s with
    | None   -> (* ev_info s "Steps: %d" n; *)
      s
    | Some e -> nstep e_st (n-1) e

(* Hack *)
let to_nf st e = nstep st 1000 e

(* Only primitives, constants, unbound variables and application of
   them *)
(* EG: This should become redundant if we are going to be normalizing *)
(* FIXME: implement with fold *)
let rec is_nf st e = match unloc e with
  | EPrim _s                     -> true
  | EConst _c                    -> true
  | EVar v                       -> not (is_var_bound st v)
  (* Ummmm... *)
  | EApp (e_f, e_l)                ->
    begin match unloc e_f with
    | ELam _   -> false
    | _        -> is_nf st e_f && List.for_all (is_nf st) e_l
    end

  | ELam (_bi, _ty, e)           -> is_nf st e
  | ECs  _n                      -> true
  | EMatch (_asy, e_m, _p, _ty)  -> is_nf st e_m
  | EMUnit (_, e_u)              -> is_nf st e_u
  | _ ->
    ev_info e "Arbitrary expression: @[%a@] understood not to be in NF" P.pp_exp e;
    false
