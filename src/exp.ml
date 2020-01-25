(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Parsetree
open EC.Location
open Constants

(* Miscellanous random bits for dealing with expressions, most of it will
   eventually be moved elsewhere *)

let error loc msg = raise (ParseError (loc, msg))

(* This module captures the state of an expression *)
module ExpState = struct

let fo_init () =

  let open Env                                                             in
  let open WhyImport                                                       in

  let e = empty                                                            in

  (* Logical conectives *)
  let e = add_type e tprop_info []                                         in

  let e = add_prim e (builtin_th, l_not)  ty_boolop1                       in
  let e = add_prim e (builtin_th, l_and)  ty_boolop2                       in
  let e = add_prim e (builtin_th, l_or)   ty_boolop2                       in
  let e = add_prim e (builtin_th, l_impl) ty_boolop2                       in

  (* Core theories *)
  let e = load_why3_theory builtin_th e                                    in
  let e = load_why3_theory bool_th    e                                    in
  let e = load_why3_theory ho_th      e                                    in

  let e = Array.fold_left (fun e n ->
          load_why3_theory (tuple_th n) e) e @@ Array.init 10 (fun x -> x) in

  let e = load_why3_theory distr_th   e                                    in

  (* Forall needs the functional type *)
  let e = add_prim e (builtin_th, l_all) ty_quant                          in

  (* Required for the monad *)
  let e = load_why3_theory real_th    e                                    in

  e

  type exp_st_rec = {
    env               : Env.env;

    (* Name of the file *)
    name              : string;

    (* Whether we will trust VC, in which case they are relegated to a
       why3 file *)
    trust             : string option;

    (* FIXME: This has to go away and be replace with a proper PCF typer *)
    in_assertion : bool;
  }

  type exp_st = exp_st_rec located

  let getenv     st   = (unloc st).env
  let update_env st f = lmap (fun st -> {st with env = f st.env}) st
  let with_env   st f = f (unloc st).env

  (* Builtins *)

  let initial name = mk_loc _dummy
    {
      env               = fo_init ();
      name              = name;
      trust             = None;
      in_assertion      = false;
    }

  let empty = mk_loc _dummy
    {
      env               = Env.empty;
      name              = "";
      trust             = None;
      in_assertion      = false;
    }

  let enable_ass   = lmap (fun st -> { st with in_assertion = true;  })
  let disable_ass  = lmap (fun st -> { st with in_assertion = false; })

  let enable_trust vc  = lmap (fun st -> { st with trust = Some vc;  })
  let mk_vc_file st n  = let st = unloc st in
                         Option.map (fun tn -> st.name ^ "_vc_" ^ tn ^ "_" ^ (string_of_int n) ^ ".why") st.trust

  let open_binder  st bi ty = lmap (fun st ->
    { st with
      env = Env.extend_bi bi ty st.env;
    }) st

  let extend st n rel opaque ty =
    let (bi, n_env) = Env.extend n rel opaque ty (getenv st) in
    (bi, update_env st (fun _ -> n_env) )

  let access st idx =
    Env.access (unloc st).env idx

  let prim_type st p = snd @@ Env.lookup_prim (getenv st) p
  let cons_type st c = snd @@ Env.lookup_cons (getenv st) c

  let type_info st ty = (fst @@ Env.lookup_type (getenv st) ty, ty)
  let cons_info st cs = (fst @@ Env.lookup_cons (getenv st) cs, cs)

end

open ExpState

module Builders = struct

  let make_var idx bi env =
    EVar {
      v_binfo = bi;
      v_index = idx;
      v_side  = SiNone;
      v_size  = Env.length env;
    }

  let make_rvar idx bi side env =
    EVar {
      v_binfo = bi;
      v_index = idx;
      v_side  = side;
      v_size  = Env.length env;
    }

  (* Resolve ident either to a primitive or to a HO binding. The
     seconds has always preference. *)
  let resolve_ident env loc id side =
    (* Try first the HO bindings *)
    mk_loc loc @@

      match Env.lookup id env with
      | Some (idx, bi, _ty) ->
        begin match side with
        | None      -> make_var  idx bi      env
        | Some side -> make_rvar idx bi side env
        end

    (* Try the FO binders *)
      | None        ->
        begin match side with
        | None      ->
          begin
            try let (th, _ty) = Env.lookup_prim env id in
                EPrim (th, id)
            with Not_found -> error loc (Some ("Identifier " ^ id ^ " not bound!"))
          end
        | Some _           -> error loc (Some ("Identifier " ^ id ^ " is not relational or not declared, cannot resolve side!"))
        end

  let mk_from_id st id =
    resolve_ident (getenv st) (getloc st) id None

  let mk_loc (st : 'a located) e = mk_loc st.pl_loc e

  (* Expression and type builders *)
  let mk_exp_float st v =
    mk_loc st @@ EConst (ECReal v)

  let mk_exp_prim st p =
    mk_loc st @@ EPrim p

  let mk_exp_cs st p =
    mk_loc st @@ ECs p

  let mk_exp_var st idx bi =
    mk_loc st @@ make_var idx bi (getenv st)

  let mk_exp_lam st bi ty e =
    mk_loc st @@ ELam(bi, ty, e)

  let mk_exp_app st f arg =
    mk_loc st @@ EApp(f, arg)

  (* EG: We could improve this *)
  let mk_app_list e largs =
    EC.Location.mk_loc e.pl_loc @@ EApp(e, largs)

  let mk_exp_tuple l n e = mk_app_list (EC.Location.mk_loc l (ECs (tuple_th n, "Tuple"  ^ (string_of_int n)))) e

  let mk_exp_bin st op e1 e2 =
    let op_exp = mk_from_id st op                        in
    let ap1    = mk_loc st @@ EApp(op_exp, [e1])         in
    mk_loc st @@ EApp (ap1, [e2])

  (* Exp should be already bound *)
  let mk_exp_forall st bi ty exp =
    let exp_all = mk_exp_prim st (builtin_th, l_all)  in
    let exp_lam = mk_exp_lam st bi ty exp             in
    mk_exp_app st exp_all [exp_lam]

  let mk_ty_float st =
    let ty = TPrim (type_info st "real", [])   in
    mk_loc st (ty, None)

  let mk_ty_unit st e_ann =
    let ty = TPrim (type_info st "tuple0", []) in
    mk_loc st @@ (ty, e_ann)

  (*  *)
  let mk_ty_m st bi_a bi_d ty e_ann=
    mk_loc st @@ (TM (bi_a, bi_d, ty), e_ann)

  let mk_ty_c st ty e_ann=
    mk_loc st @@ (TC ty, e_ann)

  (* The issue of nested refinement types is still open *)
  let mk_ty_ref st bi b_ty ass e_ann =
    (* Kind of a hack *)
    let (b_ty, ass) = match ty_u b_ty with
      | TRef (_bi, b_ty', ass') ->
        (* We must remove one binding *)
        let nv     = mk_from_id st bi.b_name             in
        let b_ty_n = ty_subst  1 nv b_ty'                in
        let ass_n  = exp_subst 1 nv ass'                 in
        (b_ty_n, mk_exp_bin st l_and ass_n ass)
      | _ -> (b_ty, ass)
    in
    mk_loc st @@ (TRef (bi, b_ty, ass), e_ann)

end

(* open Builders *)

(* Normalize nested refinement types, even if we avoid the most
   common cases in the typer *)
(* match ty_u b_ty with *)
(* | TRef (_bi, b_ty', ass') -> *)
(*   let n_ass = mk_exp_bin l_and ass ass' in *)
(* | _ *)

(* Useless for now, they need the mythical exp_map_with_env... *)
(* let exp_sanity st e = *)
(*   let f_sanity env v = *)
(*     let (bi, _) = Env.access env v.v_index in *)
(*     assert (v.v_binfo.b_name = bi.b_name)  in *)
(*   let f_map env _ v = *)
(*     f_sanity env v; *)
(*     EVar v                                 in *)
(*   let _ = exp_map 0 (f_map (getenv st)) e  in *)
(*   () *)

(* let ty_sanity st ty = *)
(*   let f_sanity env v = *)
(*     let (bi, _) = Env.access env v.v_index in *)
(*     assert (v.v_binfo.b_name = bi.b_name)  in *)
(*   let f_map env _ v = *)
(*     f_sanity env v; *)
(*     EVar v                                 in *)
(*   let _ = ty_map 0 (f_map (getenv st)) ty  in *)
(*   () *)
