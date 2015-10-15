(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Pretty printing module, based on the standard Format facility. *)

open Format

open Env
open EcLocation
open Parsetree

open Support.Options
open Support.Util

(**********************************************************************)
(* Unicode handling *)

module Symbols = struct
  type pp_symbols =
      Inf
    | Forall
    | Exists
    | Not
    | And
    | Or
    | Arrow
    | DblArrow
    | DblColon
    | DownArrow
    | LE
    | Lollipop
    | Tensor
    | Union
    | Nat
    | Int
    | Real
    | Bool
    | Mu
    | Lambda
    | BigLambda
    | Pi
    | Fuzzy
    | SubTau

  let pp_symbol_table s = match s with
      Inf       -> ("inf",     "∞")
    | Forall    -> ("all",     "∀")
    | Exists    -> ("exists",  "∃")
    | Not       -> ("not",     "¬")
    | And       -> ("/\\",     "∧")
    | Or        -> ("‌\\/",     "∨")
    | Arrow     -> ("->",      "→")
    | DblArrow  -> ("=>",      "⇒")
    | DblColon  -> ("::",      "∷")
    | DownArrow -> ("|>",      "↓")
    | LE        -> ("<=",      "≤")
    | Lollipop  -> ("-o",      "⊸")
    | Tensor    -> ("x",       "⊗")
    | Union     -> ("+",       "⊕")
    | Nat       -> ("nat",     "ℕ")
    | Int       -> ("int",     "ℤ")
    | Real      -> ("real",    "ℝ")
    | Bool      -> ("bool",    "𝔹")
    | Mu        -> ("mu",      "μ")
    | Lambda    -> ("\\",      "λ")
    | BigLambda -> ("\\!",     "Λ")
    | Pi        -> ("Pi",      "Π")
    | Fuzzy     -> ("circle",  "◯")
    | SubTau    -> ("_t",      "ₜ")

  let string_of_symbol s =
    let select = if !debug_options.unicode then snd else fst in
    select (pp_symbol_table s)
end

let u_sym x = Symbols.string_of_symbol x

(**********************************************************************)
(* Helper functions for pretty printing *)

let pp_int ppf i = fprintf ppf "%d" i
let pp_str ppf s = fprintf ppf "%s" s

let rec pp_list pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "@[%a@]" pp csx
  | csx :: csl -> fprintf fmt "@[%a@]@;%a" pp csx (pp_list pp) csl

let rec pp_list_sep sep pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "@[%a@]" pp csx
  | csx :: csl -> fprintf fmt "@[%a@]%s@;%a" pp csx sep (pp_list_sep sep pp) csl

let rec pp_n_list n pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "{%2d} @[%a@]" n pp csx
  | csx :: csl -> fprintf fmt "{%2d} @[%a@]@;%a" n pp csx (pp_n_list (n-1) pp) csl

let pp_option pp fmt o = match o with
  | None   -> fprintf fmt "No"
  | Some v -> fprintf fmt "Yes(%a)" pp v

let pp_paren pp fmt x = fprintf fmt "(%a)" pp x

(* PP for maps *)
let pp_n_e pp ppf (n, bi) =
  fprintf ppf "[%2d] @[%a@]" n pp bi

let pp_imap pp ppf im =
  let im = RIntMap.bindings im in
  fprintf ppf "@[<v>%a@]" (pp_list (pp_n_e pp)) im

(* Study this concept *)
(* Limit a formatter: (limit_boxes 3 pp_type) *)
let limit_boxes ?(n=(!debug_options).pr_level) pp = fun fmt ->
  let mb      = Format.pp_get_max_boxes fmt () in
  let con fmt = Format.pp_set_max_boxes fmt mb in
  (* print_string "eo"; print_string (string_of_int n); print_newline (); *)
  Format.pp_set_max_boxes fmt n;
  kfprintf con fmt "%a" pp

(**********************************************************************)
(* Pretty printing for variables *)

let pp_var ppf v =
  let name   = v.v_binfo.b_name                                             in
  let opaque = if v.v_binfo.b_opaque then "" else (u_sym Symbols.DownArrow) in
  let rel    = v.v_binfo.b_rel                                              in
  let rela   = if rel then (u_sym Symbols.DblColon) else ""                 in
  let side   = match v.v_side with
    | SiNone  -> ""
    | SiLeft  -> "<1>"
    | SiRight -> "<2>"                                                      in
  let rname = name ^ opaque ^ side                                          in
  match !debug_options.var_output with
    | PrVarName  -> fprintf ppf "%s" rname
    | PrVarIndex -> fprintf ppf "[%d/%d]" v.v_index v.v_size
    | PrVarBoth  -> fprintf ppf "%s@@[%d/%d]" (rela ^ rname) v.v_index v.v_size
    (* This is a little bit special, we make some guess here *)
    | PrVarNum   -> if rel then
	fprintf ppf "%s%d%s" name v.v_index side
      else
	fprintf ppf "%s" rname

(* let pp_binfo fmt b = pp_name fmt (b.b_type, b.b_name) *)
let pp_binfo ppf b = if b.b_opaque then
    fprintf ppf "%s" b.b_name
  else
    fprintf ppf "%s%s" b.b_name (u_sym Symbols.DownArrow)

(* (\* Prints a type definition *\) *)
(* let pp_cons ppf cs = *)
(*   match cs with *)
(*   | TConstr (n, tys) -> fprintf ppf "| %s @[<h>%a@]" n (pp_list pp_ity) tys *)

let pp_ty_prim ppf n =
  fprintf ppf "%s" (snd n)
  (* fprintf ppf "%s.%s.%s" (fst (fst n)) (snd (fst n)) (snd n) *)

let pp_ty_cs ppf cs =
  fprintf ppf "%s" (snd cs)
  (* fprintf ppf "%s.%s.%s" (fst (fst cs)) (snd (fst cs)) (snd cs) *)


(* let string_of_unop op  = match op with *)
(*   | UnOpNot    -> u_sym Symbols.Not *)

(* let string_of_binop op = match op with *)
(*   | BiOpAnd    -> u_sym Symbols.And *)
(*   | BiOpOr     -> u_sym Symbols.Or *)

(* let string_of_quant qf = match qf with *)
(*   | QuantExists -> u_sym Symbols.Exists *)
(*   | QuantAll    -> u_sym Symbols.Forall *)

(* let string_of_pred pr = match pr with *)
(*   | PredLe      -> u_sym Symbols.LE *)
(*   | PredEq      -> "=" *)

let pp_econst ppf c = match c with
  (* | ECUnit      -> fprintf ppf "()" *)
  (* | ECBool b    -> fprintf ppf "%s" (if b then "true" else "false") *)
  | ECInt n     -> fprintf ppf "%d" n
  | ECReal f   -> fprintf ppf "%0.1f" f

(* Binary Operators *)
let binary_op_str s =
  if String.length s < 7 then
    None
  else
    if String.sub s 0 6 = "infix " then
      Some (String.sub s 6 (String.length s - 6))
    else
      None

let is_binary_op e = match unloc e with
  | EPrim (_, p)  -> Option.map (fun s -> s ^ "@") (binary_op_str p)
  | EVar v        -> binary_op_str v.v_binfo.b_name
  | _             -> None

let asy_to_string asy = if asy then "async " else ""

(**********************************************************************)
(* Pretty printing for expresssions                                   *)

let prim_special s = match s with
  | "all" -> (u_sym Symbols.Forall)
  | _     -> s

let somty mt = match mt with
  | Fdistance -> "f"

let somu tm = match tm with
  | PMonad -> "munit"
  | CMonad -> "cunit"
  | DMonad -> "dunit"

let soml tm = match tm with
  | PMonad -> "mlet"
  | CMonad -> "clet"
  | DMonad -> "dlet"

let sotc tc = match tc with
  | None -> ""
  | Some (n,args) -> "{struct " ^ (string_of_int n) ^ "/" ^ (string_of_int args)^ "}"

let pp_gen_bi pp fmt (bi, ppe) =
  let bi_sym = if bi.b_rel then (u_sym Symbols.DblColon) else ":" in
  fprintf fmt "%a @<1>%s @[%a@]" pp_binfo bi bi_sym pp ppe

let rec pp_pat ppf (cs, binders) =
  fprintf ppf "%a @[%a@]" pp_ty_cs cs (pp_list pp_binfo) binders

and pp_bi fmt (bi, ty) = pp_gen_bi pp_ty fmt (bi, ty)

and pp_pbi fmt bi = pp_paren pp_bi fmt bi

and pp_exp  ppf e =
  let rec gather_lam e = match unloc e with
    | ELam (bi, ty, e) -> let (r, e_r) = gather_lam e in
                          ((bi, ty) :: r, e_r)
    | _                -> ([], e)
  in
  let pp_special_lamba ppf e =
    let (arg_l, e_ret) = gather_lam e in
    fprintf ppf "@[<hov>(@<1>%s @[<hov 1>@[<v>%a@] @<1>%s@;@[%a@]@])@]"
      (u_sym Symbols.Lambda) (pp_list pp_pbi) arg_l (u_sym Symbols.Arrow) pp_exp e_ret
  in
  match unloc e with

  | EImport (th, e)                -> fprintf ppf "import %s.%s;@\n@[%a@]" (fst th) (snd th) pp_exp e
  | EConst c                       -> pp_econst ppf c
  (* Disable useless @ printing. *)
  (* | EPrim s                        -> fprintf ppf "%s@@" (snd s) *)
  | EPrim s                        -> fprintf ppf "%s" (prim_special (snd s))

  | ECs cs                         -> fprintf ppf "%a" pp_ty_cs cs
  | EMatch (asy, e_m, cases, r_ty) -> fprintf ppf "%smatch @[%a@] with %a@\n@[<v 1> %a@]" (asy_to_string asy)
                                                   pp_exp e_m pp_tya r_ty (pp_list pp_mcase) cases

  | EVar   vi                      -> fprintf ppf "%a" pp_var vi

  | ELam   (bi, ty, e_i)           -> pp_special_lamba ppf e

  | EApp    (e_f, e_l)             -> pp_special_app ppf e_f e_l

  | ELet   (bi, tr, ty, e1, e2)   -> let let_n = match tr with
                                                 | None    -> "let"
                                                 | Some tn -> "trust ["^(tn)^"]"
                                     in
                                     fprintf ppf "@[@[<hov>%s @[%a@] =@;@[%a@]@] in@\n@[%a@]@]" let_n
                                       pp_bi (bi, ty) pp_exp e1 pp_exp e2

  | EFix   (bi, ty, tc, e)        -> fprintf ppf "@[<hov 1>fix (%a : @[%a@])%s@;@[%a@]@]"
                                                     pp_binfo bi pp_ty ty (sotc tc) pp_exp e

  | EMUnit (tm, e)                -> fprintf ppf "%s %a" (somu tm) pp_exp e
  | EMLet  (tm, bi, ty_a, e1, e2) -> fprintf ppf "@[@[<hov>%s @[%a@] =@;@[%a@]@] in@[%a@]@\n@[%a@]@]"
				                  (soml tm) pp_binfo bi pp_exp e1 pp_tya ty_a pp_exp e2

  (* May be used in the future for some more fancy printing *)
  (* | EPair   (e1, e2)             -> fprintf ppf "(%a, %a)" pp_exp e1 pp_exp e2 *)
  (* | ELetPair(b1, b2, ep, e)      -> fprintf ppf "let (%a, %a) = %a in@\n %a" *)
  (*                                                pp_binfo b1 pp_binfo b2 pp_exp ep pp_exp e *)
  (* | ENil ty                       -> fprintf ppf "[][@[%a@]]" pp_ty ty *)
  (* | ECons(x,xs)                   -> fprintf ppf "(%a :: %a)" pp_exp x pp_exp xs *)

and pp_tya ppf ty_a = match ty_a with
  | None    -> ()
  | Some ty -> fprintf ppf " [@[%a@]]" pp_ty ty

and pp_mcase ppf (pat, e) =
  fprintf ppf "| %a -> @[%a@]" pp_pat (unloc pat) pp_exp e

and pp_ty_r   ppf ty_r =
  (* Summarize all the Pi arguments *)
  let rec gather_pi ty = match fst (unloc ty) with
    | TPi (bi, tya, ty) -> let (r, ty_r) = gather_pi ty in
                           ((bi, tya) :: r, ty_r)
    | _                 -> ([], ty)
  in
  let pp_special_pi ppf bi tya ty =
    let (arg_l, ty_ret) = gather_pi ty in
    fprintf ppf "@[<hov 1>@<1>%s @[<hov>@[<v>%a@].@;@[%a@]@]@]" (u_sym Symbols.Pi)
      (pp_list pp_pbi) ((bi, tya) :: arg_l) pp_ty ty_ret
  in
  match ty_r with
  | TVar tv              -> fprintf ppf "@[%a@]" pp_tvar !tv
  (* | TVar tv              -> fprintf ppf "@[%a@]@@(%x)" pp_tvar !tv (2 * (Obj.magic tv)) *)
  | TQVar v              -> fprintf ppf "'%s" v
  | TPrim(tc, targs)     -> pp_ty_ind ppf tc targs
  | TPi (bi, tya, ty)    -> pp_special_pi ppf bi tya ty
  | TC ty                -> fprintf ppf "@[<hov 1>C@;@[<1>%a@]@]" pp_ty ty
  | TM (ea,  ed, ty)     -> fprintf ppf "@[<hov 1>M[@[%a@],@;@[%a@]]@;@[<1>%a@]@]" pp_exp ea pp_exp ed pp_ty ty
  | TG (mty, ed, ty)     -> fprintf ppf "@[<hov 1>D_%s[@[%a@]]@;@[<1>%a@]@]" (somty mty) pp_exp ed pp_ty ty
  | TRef (bi, ty, fo)    -> fprintf ppf "@[<hov 2>{ @[%a@]@;|@[<1> %a@] }@]" pp_bi (bi, ty) pp_exp fo
  (* | TPair (ty1, ty2)     -> fprintf ppf "(%a * %a)" pp_ty ty1 pp_ty ty2 *)

and pp_ty_ind ppf i l = match l with
  | []   -> fprintf ppf "@[%a@]" pp_ty_prim i
  | [ty] -> fprintf ppf "@[%a@] @[%a@]" pp_ty_prim i pp_ty ty
  | l    -> fprintf ppf "@[%a@] (@[<h>%a@])" pp_ty_prim i (pp_list_sep "," pp_ty) l

and pp_ty ppf t = let (ty, e) = unloc t in match e with
  | None      -> pp_ty_r ppf ty
  | Some eann ->
    if !debug_options.exp_ann then
      fprintf ppf "@[%a@]@;!!{@[%a@]}" pp_ty_r ty pp_eann eann
    else
      pp_ty_r ppf ty

and pp_tvar ppf tv = match tv with
  | TV_Free s          -> fprintf ppf "?%s" s
  | TV_Link ty         -> fprintf ppf "!%a" pp_ty ty

and pp_eann ppf (el, er) =
  fprintf ppf "@[%a@] ~ @[%a@]" pp_exp el pp_exp er

(* Print infix operators *)
and pp_special_app ppf e_f e_l =
  let pp_app_inner ppf e = match unloc e with
    | EApp _ -> fprintf ppf "(@[<hov>%a@])" pp_exp e
    | _      -> fprintf ppf "@[<hov>%a@]"   pp_exp e
    (* | _      -> fprintf ppf "@[<hov>%a@]"   pp_exp e *)
  in
  let regular_print e_f e_l = match e_l with
    | []  -> fprintf ppf "%a" pp_exp e_f
    | [a] -> fprintf ppf "%a@;<1 1>@[%a@]"   pp_exp e_f pp_app_inner a
    | _   -> fprintf ppf "%a@;<1 1>@[[%a]@]" pp_exp e_f (pp_list_sep " #" pp_app_inner) e_l
  in
  let detect_infix e_f e_l =
    match unloc e_f, e_l with
    |       op, [arg_1;    arg_2] ->
        Option.map (fun s -> (s, arg_1, arg_2)) (is_binary_op e_f)
    | EApp (op, [arg_1]), [arg_2] ->
        Option.map (fun s -> (s, arg_1, arg_2)) (is_binary_op op)
    | _ -> None
  in
  match detect_infix e_f e_l with
  | None              -> regular_print e_f e_l
  | Some (op, a1, a2) -> fprintf ppf "@[%a@] %s@ @[%a@]" pp_exp a1 op pp_exp a2

  (* | TmApp(_, TmApp(_, TmVar(_, v), cond), op1) -> *)
  (*   if v.v_name = "if_then_else" then *)
  (*     fprintf ppf "@[<v>if @[<hov>%a@] then@ @[<h>%a@]@,else@ @[%a@]@]" pp_term cond pp_term op1 pp_term tm2 *)


(* and pp_fo ppf f = match unloc f with *)
(*   | FUnOp  (op, fo)          -> fprintf ppf "%s %a"     (string_of_unop op) pp_fo fo *)
(*   | FBinOp (op, f1, f2    )  -> fprintf ppf "%a %s %a"  pp_fo f1 (string_of_binop op) pp_fo f2 *)
(*   | FQuant (qf, bi, ty, fo)  -> fprintf ppf "%s %a. %a" (string_of_quant qf) pp_bi (bi, ty) pp_fo fo *)
(*   | FPred  (p,  e1, e2)      -> fprintf ppf "%a %s %a"  pp_exp e1 (string_of_pred p) pp_exp e2 *)

(**********************************************************************)
(* Pretty printing for environments *)

let pp_env n = pp_n_list n pp_bi

let pp_env ppf env =
  fprintf ppf "[@[<v>%a@]@\n]" (pp_env (List.length env - 1)) (List.rev env)

