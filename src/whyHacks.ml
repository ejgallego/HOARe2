(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Some hacks and redefitions of Why3 type inference *)

open Why3.Ty
open Why3.Term

let rec ty_inst s ty = match ty.ty_node with
  | Tyvar n -> Mtv.find_def ty n s
  | _ -> ty_map (ty_inst s) ty

let rec ty_match s ty1 ty2 =
  match ty1.ty_node, ty2.ty_node with
    (* Printf.printf "matching"  *)
    | Tyapp (f1,l1), Tyapp (f2,l2) when ts_equal f1 f2 ->
        List.fold_left2 ty_match s l1 l2
    | Tyvar n1, _  ->
      begin
        try let ty1 = Mtv.find n1 s                     in
            ty_match s (ty_inst s ty1) (ty_inst s ty2)
        with Not_found -> Mtv.add n1 (ty_inst s ty2) s
      end
    | _ , Tyvar n2 ->
      begin
        try let ty2 = Mtv.find n2 s                     in
            ty_match s (ty_inst s ty2) (ty_inst s ty1)
        with Not_found -> Mtv.add n2 (ty_inst s ty1) s
      end
    | _ -> Format.printf "Error type %a vs %a%!"
                 Why3.Pretty.print_ty ty1 Why3.Pretty.print_ty ty2;
      raise Exit

let ty_match s ty1 ty2 =
  try ty_match s ty1 ty2
  with Exit -> raise (TypeMismatch (ty_inst s ty1, ty2))

let ls_arg_inst ls tl =
  let mtch s ty t = ty_match s ty (t_type t) in
  try List.fold_left2 mtch Mtv.empty ls.ls_args tl with
    | Invalid_argument _ -> raise (BadArity (ls, List.length tl))

