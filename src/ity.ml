(* We allow polymorphism only in inductive types, thus mirroring Why3 behavior *)
type ity =
  (* Unificiation variables *)
  | TI_Var     of ity_var ref
  (* Quantified variables, only occur in the enviroment *)
  | TI_QVar    of string
  (* Primitive Inductive type: Type constructor + Parameters *)
  | TI_Type    of ity_prim * ity list

and ity_var =
  | TI_Free of string
  | TI_Link of ity

let rec ity_map f ity = match ity with
  | TI_Var  v         -> v := ity_var_map f !v; TI_Var v
  | TI_QVar v         -> f v
  | TI_Type (n, args) -> TI_Type (n, (List.map (ity_map f) args))

and ity_var_map f ity_v = match ity_v with
  | TI_Free s   -> TI_Free s
  | TI_Link ity -> TI_Link (ity_map f ity)

(* Generating fresh type variables *)
let ity_var_fresh =
  let counter = ref 0 in
  fun () ->
    let f = !counter                      in
    incr counter;
    let v_name =  "T" ^ (string_of_int f) in
    TI_Var (ref (TI_Free v_name))

module OrderedQVar = struct
  type t = string

  let compare = Pervasives.compare
end

module QVarSet = Set.Make(OrderedQVar)

(* Free quantified variables *)
let rec ity_fv ity : QVarSet.t = match ity with
  | TI_Var  v        -> ity_var_fv !v
  | TI_QVar v        -> QVarSet.add v QVarSet.empty
  | TI_Type(n, args) -> List.fold_left (fun vs ity -> QVarSet.union vs (ity_fv ity)) QVarSet.empty args

and ity_var_fv ity_v : QVarSet.t = match ity_v with
  | TI_Free s   -> QVarSet.empty
  | TI_Link ity -> ity_fv ity

let ity_instantiate ity =
  let fv      = QVarSet.elements @@ ity_fv ity                 in
  let freshv  = List.map (fun v -> (v, ity_var_fresh ())) fv   in
  let subst v = List.assoc v freshv                            in
  ity_map subst ity

let ity_instantiate_list ity_l =
  let fv_l    = List.map ity_fv ity_l                          in
  let fv      = QVarSet.elements @@ List.fold_left
    (fun vs1 vs2  -> QVarSet.union vs1 vs2) QVarSet.empty fv_l in
  let freshv  = List.map (fun v -> (v, ity_var_fresh ())) fv   in
  let subst v = List.assoc v freshv                            in
  List.map (ity_map subst) ity_l

exception Unify of ity * ity

let rec ity_eq ity1 ity2 = match ity1, ity2 with
  | TI_Var {contents = TI_Link t1}, t2
  | t1, TI_Var {contents = TI_Link t2}        -> ity_eq t1 t2

  | TI_Var {contents = TI_Free v1}, TI_Var {contents = TI_Free v2} -> v1 = v2

  | TI_Type (n1, a1), TI_Type (n2, a2)        -> n1 = n2 && begin
                                                   try List.for_all2 ity_eq a1 a2
                                                   with Invalid_argument _ -> false
                                                 end
  | TI_QVar v1, TI_QVar v2                    -> v1 = v2
  | _, _                                      -> false

(* FIXME: *)
let rec occurs t ot = ()

(* Based on the actual Ocaml code (see okmij.org/ftp/ML/generalization.html) *)
(* Note that the above code seems to have a bug when trying to unify !T = T *)

let rec ity_unify ity1 ity2 =
  (* Printf.printf "Calling unify: %a, %a%!" Print.pp_ity ity1 Print.pp_ity ity2; *)
  if ity1 == ity2 then ()
  else match ity1, ity2 with
  (* Unlink first *)
  | TI_Var {contents = TI_Link t1}, t2
  | t1, TI_Var {contents = TI_Link t2}        ->
    ity_unify t1 t2
  | TI_Var ({contents = TI_Free _} as tv), t'
  | t', TI_Var ({contents = TI_Free _} as tv) ->
    occurs tv t';
    tv := TI_Link t'
  | TI_Type (n1, a1), TI_Type (n2, a2)        ->
    if n1 = n2 && List.length a1 == List.length a2 then
      try List.iter2 (fun t1 t2 -> ity_unify t1 t2) a1 a2
      with Unify _   -> raise (Unify (ity1, ity2))
    else raise (Unify (ity1, ity2))
  (* Hack *)
  | TI_QVar v1, TI_QVar v2                    -> if v1 <> v2 then raise (Unify (ity1, ity2))
  | _, _                                      -> raise (Unify (ity1, ity2))

type constr =
  (* name    types of params     return type*)
  TConstr of string * ity list

type ity_def = string * constr list

