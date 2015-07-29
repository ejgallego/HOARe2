(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

val resolve_why3_theory : Parsetree.th_info -> Why3.Theory.theory
val load_why3_theory    : Parsetree.th_info -> Env.env -> Env.env

