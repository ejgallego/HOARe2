(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open List
open Format
open Parsetree
open Support.Error
open Support.Util

module L    = EcLocation
module P    = Print
module Opts = Support.Options

let term_error   fi   = error_msg Opts.Termination fi

let term_warning fi   = message 1 Opts.Termination fi
let term_info    fi   = message 2 Opts.Termination fi
let term_info2   fi   = message 3 Opts.Termination fi
let term_debug   fi   = message 4 Opts.Termination fi
let term_debug2  fi   = message 5 Opts.Termination fi
let term_debug3  fi   = message 6 Opts.Termination fi

(* Very simple and non-powerful termination checker, it builds a size
   relation between variables.

   We didn't put a lot of effort here as termination is a largely
   independent matter from the rest of the tool.

   Polymorphism and lot of other conditions will make this checker fail.
*)

type rel = (int * int) list

let pp_rel_elem ppf (d1, d2) = fprintf ppf "(%d,%d)" d1 d2
let pp_rel ppf rel = fprintf ppf "[%a]" (P.pp_list_sep "," pp_rel_elem) rel

let rel_shift n b rel =
  let sh_f v = if v >= b then v + n else v in
  map (fun (v1, v2) -> (sh_f v1, sh_f v2)) rel

(* No cycles can be built for now *)
let build_reach rel n =
  let rec build_reach_aux acc rel n =
    let one_step = IntSet.of_list @@ map snd @@ filter (fun (x,r) -> x = n) rel in
    let new_acc  = IntSet.union acc one_step in
    if IntSet.equal acc new_acc then
      acc
    else
      build_reach_aux new_acc rel n
  in
  build_reach_aux IntSet.empty rel n

let is_sub rel n1 n2 =
  let reach = build_reach rel n1 in
  IntSet.mem n2 reach

(* The termination checker itself *)
let rec term_check n rel pos e =
  term_debug3 e "TermCheck for exp @[%a@] rel: @[%a@]" P.pp_exp e pp_rel rel;
  let u_e = exp_uncurry e in
  let res =
  match L.unloc u_e with
  | EImport _
  | EConst _
  | EPrim  _
  | ECs    _        -> true
  | EMUnit (_, e_u) -> term_check n rel pos e_u

  | ELet  (_, _, _, e1, e2)
  | EMLet (_, _, _, e1, e2) ->
    term_check n      rel                pos e1 &&
    term_check (n+1) (rel_shift 1 0 rel) pos e2

  (* The recursor cannot appear in any argument but as a head of application *)
  | EVar v -> not (v.v_index = n)

  (* Functions *)
  | ELam (_, _, e_l)  ->
    term_check (n+1) (rel_shift 1 0 rel) pos e_l

  (* Main cases *)
  | EApp (e_f, e_l) ->
    begin
      match L.unloc e_f with
      (* v is the variable bound by fix *)
      | EVar v when v.v_index = n ->
        begin
          if List.length e_l > pos then
            let rec_exp = List.nth e_l pos in
            match L.unloc rec_exp with
            (* We only allow recursive application to another variable *)
            | EVar v ->
              term_debug3 e_f "Checking %d is sub %d" (pos + n) v.v_index;
              let res = is_sub rel (n - pos - 1) v.v_index in
              if not res then
                term_warning e_f "Failed subterm check for %a in recursive call" P.pp_exp rec_exp;
              res
            | _      -> false
          else
            false
        end
      (* We are on a different call, we should be fine if all the terms are *)
      | _ ->
        term_check n rel pos e_f &&
        for_all (term_check n rel pos) e_l
    end
  (*  *)
  | EMatch (_, e_m, cases, _) ->
    let check_branch f_rel (p, b_e) =
      let nb = List.length @@ snd @@ L.unloc p in
      term_check (n + nb) (f_rel nb) pos b_e
    in
    let f_rel_add rel v nv =
      let sh_rel = rel_shift nv 0 rel in
      let rec mk_new n = if n > 0 then
          (v + nv, n - 1) :: mk_new (n - 1)
        else []
      in
      let rel_new = mk_new nv in
      sh_rel @ rel_new
    in
    begin
      (* If we match on a variable, we add it to the relation *)
      match L.unloc e_m with
      | EVar v ->
        (* We add v to the relation *)
        let f_fn = f_rel_add rel v.v_index in
        for_all (check_branch f_fn) cases
      (* Not a variable, not adding anything then ... *)
      | m ->
        let f_fn _ = rel in
        term_check n rel pos e_m &&
        for_all (check_branch f_fn) cases
    end

  (* Shouldn't be hard to enable *)
  | EFix (bi, ty, tc, e) -> false

  in
  term_debug2 e "TermCheck for exp @[%a@] result: @[%b@]" P.pp_exp e res;
  res

let check st e (pos, n_args) =
  if Opts.comp_enabled Opts.Termination then
    (* We assume 0 to contain the recursor *)
    term_check 0 [] pos e
  else
    true

