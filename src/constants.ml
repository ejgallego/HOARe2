(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Parsetree
open EC.Location

(* Information about builtins theories, must be kept in sync with Why3 *)
let builtin_th = (""    , "BuiltIn"   )
let bool_th    = (""    , "Bool"      )
let ho_th      = (""    , "HighOrd"   )
let distr_th   = ("rlc" , "Distr"     )

(* Required for typing the monad     *)
let real_th    = ("real", "RealInfix" )

(* This should correspond to the builtin theory *)
let tprop_info  = (builtin_th, "prop")
let tint_info   = (builtin_th, "int")
let treal_info  = (builtin_th, "real")
let tdistr_info = (distr_th,   "distr")
let tfunc_info  = (ho_th,      "func")

let il t = mk_loc _internal (t, None)

let ty_int      = il @@ TPrim (tint_info,  [])
let ty_real     = il @@ TPrim (treal_info, [])

let typ_prop    = TPrim (tprop_info, [])
let ty_prop     = il typ_prop

let mk_arrow t1 t2 = il (TPi(_dbi, t1, t2))

let ty_boolop1 = mk_arrow ty_prop ty_prop
let ty_boolop2 = mk_arrow ty_prop ty_boolop1

let ty_fv     = il (TQVar "a")
let ty_quant  = mk_arrow (mk_arrow ty_fv ty_prop) ty_prop

let ty_tuple_name n  = "tuple" ^ (string_of_int n)
let cs_tuple_name n  = "Tuple" ^ (string_of_int n)
let tuple_th n  = ("", cs_tuple_name n)

let ty_tuple args =
  let n  = List.length args                in
  TPrim ((tuple_th n, ty_tuple_name n), args)

(* This is suspicious *)
let exp_unit  = ECs (tuple_th 0, cs_tuple_name 0)
let dummy_e   = mk_loc _dummy @@ exp_unit

let exp_int   i = EConst (ECInt i)
let exp_float f = EConst (ECReal f)

(* Constants for operators, must be kept in sync with the lib *)
let eq_op     = "infix ="

let add_float = "infix +."
let mul_float = "infix *."
let le_float  = "infix <=."

let l_and     = "infix /\\"
let l_or      = "infix \\/"
let l_impl    = "infix =>"
let l_not     = "not"

let l_all     = "all"
