(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Parsetree

module WEnv = Why3.Env
module WT   = Why3.Theory
module WP   = Why3.Pretty

module I  = Why3.Ident
module D  = Why3.Decl
module T  = Why3.Term
module Ty = Why3.Ty

module E  = Exp
module EB = E.Builders
module EC = Constants
module ES = Exp.ExpState

module L  = EcLocation
module P  = Print

open Support.Error
module Opts = Support.Options

open WhyHacks

(* Printing routines *)
open Format

let dummy_e = L.mk_loc L._dummy @@ EC.exp_unit

let why_error   fi   = error_msg Opts.SMT fi
let why_warning fi   = message 1 Opts.SMT fi
let why_info    fi   = message 2 Opts.SMT fi
let why_info2   fi   = message 3 Opts.SMT fi
let why_debug   fi   = message 4 Opts.SMT fi
let why_debug2  fi   = message 5 Opts.SMT fi
let why_debug3  fi   = message 6 Opts.SMT fi

(* Non-translatable things can be recovered *)
exception BailTranslation

let reloc e_l e = L.mk_loc e_l.L.pl_loc e

(************************************************************************ *)
(* Translation environment                                                *)

(* In our setting, Debruijn variables can be mapped to a Why3 lsymbol
   or to a why3 vsymbol
*)

type mapT =
| LS of T.lsymbol
| VS of T.vsymbol

let ls_mapT mt = match mt with
  | LS ls -> Some ls
  | VS _  -> None

let pp_mapT ppf mt = match mt with
  | LS ls -> WP.print_ls ppf ls
  | VS vs -> WP.print_vs ppf vs

let ty_mapT mt = match mt with
  | LS ls -> (ls.T.ls_args, Ty.oty_type ls.T.ls_value)
  | VS vs -> ([], vs.T.vs_ty)

let t_prim ls =
  T.t_app ls [] ls.T.ls_value

let term_mapT mt = match mt with
  | LS ls -> t_prim ls
  | VS vs -> T.t_var vs

(* Map from Debruijn index plus side to Why3 *)
module OrderedVarSide = struct
  type t = (int * var_side)
  let compare (idx1, side1) (idx2, side2) =
    let ic = - Pervasives.compare idx1 idx2 in
    if ic <> 0 then
      ic
    else
      Pervasives.compare side1 side2
end

(* We could have used a list *)
module VM = Why3.Extmap.Make(OrderedVarSide)

let pp_vm_bi ppf ((i, s), mt) = fprintf ppf "(%d<%s>) -> %a" i (string_of_side s) pp_mapT mt

let pp_vm ppf vmap = fprintf ppf "@[<v>%a@]" (P.pp_list pp_vm_bi) vmap

type w_env = {
  v_map : mapT VM.t;
  w_loc : L.t;
}

(* Shifthing our w_env *)
let w_env_shift w_st n = { w_st with
  v_map = VM.translate (fun (v,s) -> (v + n, s)) w_st.v_map;
}

(* EG: Not needed *)
(* Remove negative binders *)
(* let vm_cleanup () = vmap := VM.filter (fun v _ -> v >= 0) !vmap *)

(* EG: Must fix the mess with loc *)
let ld w_env = L.mk_loc w_env.w_loc ()

let new_env st = {
  v_map = VM.empty;
  w_loc = L.getloc st;
}

let get_var w_st v =
  let v_idx = (v.v_index, v.v_side) in
  try VM.find v_idx w_st.v_map
  with Not_found ->
    why_error (ld w_st) "Variable %a not found in Why3 ST@\n%a" P.pp_var v pp_vm (VM.bindings w_st.v_map)

let add_fs_binding w_st v_idx b =
  let map   = w_st.v_map            in
  {w_st with v_map =
      if VM.mem v_idx map then
        why_error (ld w_st) "Binding for (%d,%s) already exists" (fst v_idx) (string_of_side (snd v_idx))
          pp_mapT (VM.find v_idx map)
      else
        VM.add v_idx b map
  }

(* We can flatten types to Why3 format if needed *)
let rec flatten_wtype (ty : Ty.ty) : (Ty.ty list * Ty.ty) =
  let open Ty in
  match ty.ty_node with
  | Tyapp (ts, [t1;t2]) when ts_equal ts ts_func ->
    let (t_rest, t_ret) = flatten_wtype t2 in
    (t1 :: t_rest, t_ret)
  | _ -> ([], ty)

let make_w_var idx bi side w_ty =
  let vs_name   = I.id_fresh (bi.b_name ^ (string_of_side side)) in
  let vs        = T.create_vsymbol vs_name w_ty                  in
  ((idx, side), vs)

(* We introduce the full type now. *)
let make_w_ls idx bi side w_ty =
  let fs_name      = I.id_fresh (bi.b_name ^ (string_of_side side)) in
  let fs           = T.create_fsymbol fs_name [] w_ty               in
  ((idx, side), fs)

(* Flattening version *)
(*
let make_w_ls idx bi side w_ty =
  let (args, ty_r) = flatten_wtype w_ty                             in
  let fs_name      = I.id_fresh (bi.b_name ^ (string_of_side side)) in
  let fs           = T.create_fsymbol fs_name args ty_r             in
  ((idx, side), fs)
*)

let vm_add w_st k b = {w_st with
  v_map = VM.add k b w_st.v_map;
}

(* Adds a variable to the context *)
let add_variable w_st bi (w_ty : Ty.ty) =
  (* If the binding is relational we actually add two variables, but shift only once *)
  let sh_st = w_env_shift w_st 1 in

  if bi.b_rel then
    let (v1, vs1) = make_w_var 0 bi SiLeft  w_ty in
    let (v2, vs2) = make_w_var 0 bi SiRight w_ty in
    let w_st'     = vm_add sh_st v1 (VS vs1)     in
    ([vs1; vs2], vm_add w_st' v2 (VS vs2))
  else
    let (v, vs) = make_w_var 0 bi SiNone w_ty in
    ([vs], vm_add sh_st v (VS vs))

(* Add a function definition *)
let add_fdef w_st idx bi w_ty =
  (* If the binding is relational we actually add two variables *)
  if bi.b_rel then
    let (v1, ls1) = make_w_ls idx bi SiLeft  w_ty in
    let (v2, ls2) = make_w_ls idx bi SiRight w_ty in
    let w_st' = add_fs_binding w_st v1 (LS ls1)  in
    add_fs_binding w_st' v2 (LS ls2)
  else
    let (v, ls)   = make_w_ls idx bi SiNone  w_ty in
    add_fs_binding w_st v (LS ls)

(* Get decls *)
let w_decl w_st =
  let decls = List.map snd @@ VM.bindings @@ VM.map ls_mapT w_st.v_map in
  Option.omap D.create_param_decl decls

(************************************************************************ *)
(* Type translation                                                       *)

let why3_lookup_ty (th, ty) =
    let th = WhyImport.resolve_why3_theory th in
    WT.ns_find_ts th.WT.th_export [ty]

let rec rtype_to_why3 ty = match ty_u ty with
  (* Bound type variable *)
  | TVar ({contents = TV_Link ty_i}) ->
    rtype_to_why3 ty_i

  (* Free variables:
     NOTE: We may need a vmap here.
  *)
  | TQVar s
  | TVar ({contents = TV_Free s}) ->
    Ty.ty_var (Ty.create_tvsymbol (I.id_fresh s))

  (* Regular inductive type *)
  | TPrim (ty_i, args) -> begin
    try
      let t_args = List.map rtype_to_why3 args in
      let t_i    = why3_lookup_ty ty_i       in
      Ty.ty_app t_i t_args
    with Not_found -> why_warning dummy_e "Type %s not found" (snd ty_i);
                      raise BailTranslation
    | Ty.BadTypeArity(ty, n) -> why_warning dummy_e "Bad arity (%d) for %a." n WP.print_ts ty;
                                raise BailTranslation
  end
  | TRef (_, ty, _)     -> rtype_to_why3 ty

  | TPi (_b, ty, ty_r ) ->
    let a_ty = rtype_to_why3 ty            in
    let r_ty = rtype_to_why3 ty_r          in
    Ty.ty_app Ty.ts_func [a_ty; r_ty]

  | TC ty           -> rtype_to_why3 ty
  | TM (_a,_d, ty ) ->
    (* Hack *)
    let ts_distr = EC.tdistr_info          in
    let distr_ty = why3_lookup_ty ts_distr in
    let arg_ty   = rtype_to_why3 ty        in
    Ty.ty_app distr_ty [arg_ty]

(************************************************************************ *)
(* Term translation                                                       *)

let const_to_why3 c = match c with
  | ECInt   i -> T.t_const (Why3.Number.ConstInt (Why3.Number.int_const_dec (string_of_int i)))
  (* No words for this choice *)
  | ECReal f -> let (f,i) = modf f                                   in
		 let is    = Printf.sprintf "%.0f" i                  in
		 let fs    = String.sub (Printf.sprintf "%.3f" f) 2 3 in
		 T.t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec is fs None))

(* Special primitives *)
let why3_lprim = [
  ("infix =>",  T.Timplies);
  ("infix /\\", T.Tand);
  ("infix \\/", T.Tor);
]

let is_lprim  sym = List.mem_assoc (snd sym) why3_lprim
let get_lprim sym = List.assoc     (snd sym) why3_lprim

let why3_quant = [
  ("all",    T.Tforall);
  ("exists", T.Texists);
]

let is_quant  sym = List.mem_assoc (snd sym) why3_quant
let get_quant sym = List.assoc     (snd sym) why3_quant

let locate_prim (th, name) =
  try let th = WhyImport.resolve_why3_theory th                     in
      WT.ns_find_ls th.WT.th_export [name]
  with Not_found -> why_error dummy_e "Primitive %s cannot be found in Why3 theory %s.%s" name (fst th) (snd th)

(* Detect logical operators and forall *)
(* We could almost get rid of this given the Why3 prop/bool mess *)
let is_why3_special e_f = match L.unloc e_f with
  | EPrim  p when is_lprim p || is_quant p -> Some p
  | _                                      -> None

(* See if the first part of an application resolves to a logical primitive *)
let resolve_to_ls wst e = match L.unloc e with
  | ECs    c -> Some (locate_prim c)
  | EPrim  p -> Some (locate_prim p)
  (* A var can resolve to a primitive *)
(*  | EVar   v -> begin
    match get_var wst v with
    | LS ls  -> Some ls
    | VS _   -> None
  end
*)  | _        -> None

(* For the quantifiers *)
let expect_lamba wst e = match L.unloc e with
  | ELam (bi, ty, e_l) -> (bi, ty, e_l)
  | _                  -> why_error e "Quantifier not followed by a lambda but by @[%a@] " P.pp_exp e

let rec exp_to_why3 wst e = try match L.unloc e with
  | EConst c        -> const_to_why3 c
  | EPrim  p        -> t_prim (locate_prim p)
  | ECs    cs       -> t_prim (locate_prim cs)
  | EVar v          -> let tm = get_var wst v   in
                       term_mapT tm
  (* This is tricky *)
  | EApp (e_f, e_l) ->
    begin
    (* We first must check whether the first argument requires a
       special translation.
    *)
    match is_why3_special e_f with
    | Some p ->
      if is_lprim p then
        let w_l = List.map (exp_to_why3 wst) e_l          in
        T.t_binary (get_lprim p) (List.nth w_l 0) (List.nth w_l 1)
      (* is_quant *)
      else
        let quant        = get_quant p                    in
        (* FIXME: Irrefutable pattern matching in hd *)
        let (bi, ty, le) = expect_lamba wst (List.hd e_l) in
        let w_ty         = rtype_to_why3 ty               in
        let (w_vs, w_st) = add_variable wst bi w_ty       in
        let w_le         = exp_to_why3 w_st le            in
        let cl_term      = T.t_close_quant w_vs [] w_le   in
        T.t_quant quant cl_term

    (* The head is a standard expression *)
    | None ->
      begin
        match resolve_to_ls wst e_f with
        | Some w_ls ->
          let w_l  = List.map (exp_to_why3 wst) e_l              in

          (* Better type inference *)
          let s    = WhyHacks.ls_arg_inst w_ls w_l               in
          let w_l  = List.map (T.t_ty_subst s T.Mvs.empty) w_l   in

          T.t_app_infer w_ls w_l

        (* FIXME: If the head symbol not a primitive, we should use the
           @ HO operator, it should be easy now *)
        | None ->
          (* Hacky for now, just a test *)
          let w_f = exp_to_why3 wst e_f            in
          let w_l = List.map (exp_to_why3 wst) e_l in

          let create_app e1 e2 = T.t_app_infer T.fs_func_app [e1; e2] in
          List.fold_left (fun e arg -> create_app e arg ) w_f w_l

          (* why_warning e "STUB: cannot translate HO yet @[%a@] " P.pp_exp e; *)
          (*         raise BailTranslation *)
      end
    end

  | EMUnit (PMonad, e_m) ->
    let munit_prim = L.mk_loc e.L.pl_loc @@ EPrim(("rlc", "Distr"), "munit")  in
    let app_e      = L.mk_loc e.L.pl_loc @@ EApp (munit_prim, [e_m])          in
    exp_to_why3 wst app_e

  | EMLet(PMonad, _bi, _ty, e1, e2) ->
    why_warning e "Why3-STUB: MLet @[%a@] " P.pp_exp e;
    raise BailTranslation

  | ELet(_bi, _t, _ty, e1, e2) ->
    why_warning e "Why3-STUB: Let @[%a@] " P.pp_exp e;
    raise BailTranslation

  | ELam(_bi, _ty, e_l) ->
(*
    let e_l = 
    let id = id_user "fc" in
        let quant        = get_quant p                    in
        (* FIXME: Irrefutable pattern matching in hd *)
        let (bi, ty, le) = expect_lamba wst (List.hd e_l) in
        let w_ty         = rtype_to_why3 ty               in
        let (w_vs, w_st) = add_variable wst bi w_ty       in
        let w_le         = exp_to_why3 w_st le            in
        let cl_term      = T.t_close_quant w_vs [] w_le   in
        T.t_quant quant cl_term

  | PPquant (q, uqu, trl, e1) ->
      let qvl = List.map (quant_var uc) uqu in
      let denv = denv_add_quant denv qvl in
      let dterm e = dterm uc gvars denv e in
      let trl = List.map (List.map dterm) trl in
      let e1 = dterm e1 in
      begin match q with
        | PPforall -> DTquant (Tforall, qvl, trl, e1)
        | PPexists -> DTquant (Texists, qvl, trl, e1)
        | PPlambda ->
            let id = id_user "fc" loc and dty = dty_fresh () in
            let add acc ({id = x}, _) =
              let arg = Dterm.dterm ~loc (denv_get denv x) in
              DTapp (fs_func_app, [Dterm.dterm ~loc acc; arg]) in
            let app = List.fold_left add (DTvar ("fc",dty)) uqu in
            let f = DTapp (ps_equ, [Dterm.dterm ~loc app; e1]) in
            let f = DTquant (Tforall, qvl, trl, Dterm.dterm ~loc f) in
            DTeps (id, dty, Dterm.dterm ~loc f)
      end
*)
    why_warning e "Why3-STUB: Lambda @[%a@] " P.pp_exp e;
    raise BailTranslation

  (* Not planned for the moment *)
  | EImport _ | EFix _ | EMatch _ | EMUnit _ | EMLet _ ->
    why_warning e "Why3-STUB: Unsupported translation for @[%a@] " P.pp_exp e;
    raise BailTranslation

  with
  | Ty.TypeMismatch(ty1, ty2) ->
    why_warning e "Why3 type mismatch: @[%a@] vs @[%a@] in @[%a@] " WP.print_ty ty1 WP.print_ty ty2 P.pp_exp e;
    raise BailTranslation
  | T.BadArity (s, n) ->
    why_warning e "Why3 bad arity: @[%a@]/%d in @[%a@]" WP.print_ls s n P.pp_exp e;
    raise BailTranslation
  | T.TermExpected t -> 
    why_warning e "Why3 term expected: @[%a@] in @[%a@]" WP.print_term t P.pp_exp e;
    raise BailTranslation 

(*
      | EMatch (e, pl, ty) ->
        let e_w    = map_why3 st e                                 in
        let e_w_ty = Ty.oty_type e_w.t_ty                             in
        let p_w    = List.map (map_why3_pat st e_w_ty) pl          in
        why_info dummy_e "Point after map_pat";
        T.t_case e_w p_w

    end in
  (* why_debug3 dummy_e "Translated to Why3: @[%a@]" WP.print_term term_r; *)
    term_r

  and map_why3_pat st p_ty (cs, bl, e) =
    let n_binders             = List.length bl                    in
  (* Shift the variable map by the appropiate number of bindings *)
    vm_shift n_binders;

  (* FIXME *)
    let (cs_th, cs_ty) = Env.lookup_cons (ES.getenv st) (snd cs)  in

  (* Instantiate types of the constructors *)
    let cs_ty = Ity.ity_instantiate_list cs_ty in

  (* Introduce bindings *)
    let rec introduce_pat st bi_l ty_l = begin
      match bi_l, ty_l with
      | [], _                   -> st
      | bi :: bi_l, ty :: ty_l  ->
        let b_st = ES.open_binder st bi @@ E.ity_to_ty st [ty] in
      (* let b_st = ES.open_binder st bi (L.mk_loc b_pat.pl_loc @@ ity_to_ty st ty, None) in *)
        introduce_pat b_st bi_l ty_l
      | _ -> why_error dummy_e "Internal error in introduce_pat @[%a@]" pp_uncurry e
    end in

    let n_st = introduce_pat st bl cs_ty in

  (* Create the pattern *)
    let make_vinfo idx bi st =
      { v_binfo = bi;
        v_index = idx;
        v_side  = SiNone;
        v_size  = Env.length (ES.getenv st);
      } in

    let rec pattern_vars st n bl = match bl with
      | [] -> []
      | b :: bl -> let v      = make_vinfo n b st                 in
                   let v_w    = get_why3_var st v                 in
                   v_w :: pattern_vars st (n-1) bl
    in
    let vl                   = pattern_vars n_st (n_binders-1) bl in
    let cs_w                 = get_why3_ls cs                    in

    why_info dummy_e "Point a";
  (* Translate the expression *)
    let e_w                   = map_why3 n_st e                   in

  (* Apply the variables to the constructor *)
    let vl_w   = List.map T.t_var vl in
    let s      = WhyHacks.ls_arg_inst cs_w vl_w                   in
    let vl_w   = List.map (T.t_ty_subst s T.Mvs.empty)  vl_w      in

    let pat_e  = T.t_app_infer cs_w vl_w in
    let pat_ty = Ty.oty_type pat_e.t_ty  in

    let un_tvar t = match t.T.t_node with
      | T.Tvar v -> T.pat_var v
    in
    let bl_w   = List.map un_tvar vl_w   in

    

    why_info dummy_e "Point b, bl_w_ty :%a " WP.print_ty pat_ty;

    let pat_w                 = T.pat_app cs_w bl_w pat_ty      in

    why_info dummy_e "Pattern %a translated" WP.print_pat pat_w;

  (* Unshift the map! *)
    vm_shift (-n_binders);
  (* Remove any negative binding *)
    vm_cleanup ();
    T.t_close_branch pat_w e_w

(* val pat_wild : Ty.ty -> pattern *)
(* val pat_var : vsymbol -> pattern *)
(* val pat_app : lsymbol -> pattern list -> Ty.ty -> pattern *)
(* val pat_or : pattern -> pattern -> pattern *)

  let close_term t =
    let fvm  = T.t_freevars T.Mvs.empty t                in
    let fvbl = T.Mvs.bindings fvm                        in
    let fvl  = List.map (fun (k, _) -> k) fvbl           in
    (* let vl   = List.concat (List.map serialize_vars fvl) in *)
    T.t_forall_close fvl [] t
end

  with Ty.TypeMismatch(ty1, ty2) ->
    why_error ass "Why3 type mismatch: @[%a@] vs @[%a@]" WP.print_ty ty1 WP.print_ty ty2
    *)
