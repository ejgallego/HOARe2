(* Copyright (c) 2014, The Trustees of the University of Pennsylvania
   Copyright (c) 2014, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

module WConf = Why3.Whyconf
module WEnv  = Why3.Env
module CP    = Why3.Call_provers

open Why3

open Support.Util
open Support.Error
module Opts = Support.Options

let dummy_e = Constants.dummy_e

let why_error   fi   = error_msg Opts.SMT fi

let why_warning fi   = message 1 Opts.SMT fi
let why_info    fi   = message 2 Opts.SMT fi
let why_info2   fi   = message 3 Opts.SMT fi
let why_debug   fi   = message 4 Opts.SMT fi
let why_debug2  fi   = message 5 Opts.SMT fi
let why_debug3  fi   = message 6 Opts.SMT fi

(* We will likely borrow the EC implementation for this file *)

(*
let get_solver solver : WConf.config_prover =
  let fp      = Whyconf.parse_filter_prover solver   in
  let provers = Whyconf.filter_provers WC.config fp  in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover %s not installed or not configured@." solver;
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)

let get_driver (cfg : Whyconf.config_prover) : Driver.driver =
  try
    Driver.load_driver WC.env cfg.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for solver: %a@."
      Exn_printer.exn_printer e;
    exit 1
*)

(* let main_solvers = ["Alt-Ergo"; "CVC4"; "Eprover"; "CVC3"; "Coq"] *)
let main_solvers = ["Alt-Ergo"; "CVC4"; "Eprover"; "CVC3"]

let solvers () = List.filter EC.EcProvers.is_prover_known main_solvers

(* let s_cfg  = List.map get_solver solvers *)
(* let s_drv  = List.map get_driver s_cfg *)
(* let s_list = List.combine s_cfg s_drv *)

let load_theories task theories =
  List.fold_left (fun task th_i ->
    let th = WhyImport.resolve_why3_theory th_i in
    Task.use_export task th
  ) task theories

let load_decls task decl_map =
  List.fold_left (fun task decl ->
    match decl.Decl.d_node with
    | Decl.Dparam ls -> Task.add_param_decl task ls
    | _ -> task
  ) task decl_map

let load_axioms task axiom_map =
  RIntMap.fold (fun _n (ax_name, ax_body) task ->
    (* let ax_id = Decl.create_prsymbol (Ident.id_fresh (ax_name ^ "_p" ^ (string_of_int n))) in *)
    let ax_id = Decl.create_prsymbol (Ident.id_fresh (ax_name ^ "_rtype")) in
    Task.add_prop_decl task Decl.Paxiom ax_id ax_body
  ) axiom_map task

(* Write task to a file for debug purposes *)
let write_task_file file theories ths task =

  let oc     = open_out file                      in
  let ofmt   = Format.formatter_of_out_channel oc in
  let others = Task.used_symbols ths                                    in
  let decls  = Task.local_decls task others                             in
  Format.fprintf ofmt "theory ARLC\n";
  Format.fprintf ofmt "  use import HighOrd\n";
  List.iter (fun (th_f, th_n) -> if String.length th_f > 0 then
      Format.fprintf ofmt "  use import %s.%s@\n@\n" th_f th_n) theories;
  List.iter (fun dcl -> Format.fprintf ofmt "  @[%a@]@\n" Pretty.print_decl dcl) decls;
  Format.fprintf ofmt "end\n";
  close_out oc

let coq : Whyconf.prover =
  { prover_name = "Coq"
  ; prover_version = "8.9"
  ; prover_altern = ""
  }

let write_coq_file file task =
  if EC.EcProvers.is_prover_known "Coq" then
    let oc         = open_out (file ^ ".v")             in
    let ofmt       = Format.formatter_of_out_channel oc in
    let driver     = EC.EcProvers.get_driver coq           in
    Driver.print_task driver ofmt task
  else
    why_warning dummy_e "Trying to print Coq file, but it is not supported by Why3."

let tlimit : int ref = ref 20
let mlimit : int ref = ref 1100

let post ext theories decls axioms ass loc = try

  let task    = None                                                   in

  let task    = load_theories task theories                            in
  let task    = load_decls    task decls                               in
  let task    = load_axioms   task axioms                              in

  let goal_id = Decl.create_prsymbol (Ident.id_fresh "ty_goal")        in
  let task    = Task.add_prop_decl task Decl.Pgoal goal_id ass         in

  match ext with
  (* Relegate the assertion to a why file *)
  | Some name ->
    write_task_file name theories (Task.used_theories task) task;
    Some (true, ["toFile"])

  | None ->

    (* For debug purposes *)
    write_task_file "arlc_current.why" theories (Task.used_theories task) task;
    why_debug3 dummy_e "!S! calling all the solvers....";

    let open EC.EcProvers in

    let arlc_pi = { dft_prover_infos with
                    pr_maxprocs  = 2
                  ; pr_provers   = solvers ()
                  ; pr_timelimit = !tlimit
                  } in

    let res = EC.EcProvers.execute_task arlc_pi task in

    if Option.is_none res then begin
      let (l,c) = loc.EC.EcLocation.loc_start in
      let name = "fail_ass_" ^ (string_of_int l) ^ "_" ^ (string_of_int c) in
      write_coq_file name task
    end;
    res

(*
    let rec call_solvers solvers = match solvers with
      | []     -> false
      | (s_cfg, s_drv) :: ss ->
        let s_result : Call_provers.prover_result =
          Call_provers.wait_on_call
            (Driver.prove_task
               ~command:s_cfg.Whyconf.command
               ~timelimit:!tlimit
               ~memlimit:!mlimit
  	       s_drv task ()) ()
        in
        let s_name = s_cfg.Whyconf.prover.Whyconf.prover_name in
        why_info dummy_e "!S! @[%s answers %a@]" s_name Call_provers.print_prover_result s_result;

        match s_result.CP.pr_answer with
        | CP.Valid   -> true
        | _          -> call_solvers ss
    in
    call_solvers s_list

*)

  with Decl.UnknownIdent s -> why_error dummy_e "Unkwown identifier at task: %s" s.Ident.id_string

  (* | CP.Invalid -> false *)
  (* | Timeout *)
  (*     (\** the task timeout, ie it takes more time than specified *\) *)
  (* | OutOfMemory *)
  (*     (\** the task timeout, ie it takes more time than specified *\) *)
  (* | Unknown of string *)
  (*     (\** The prover can't determine if the task is valid *\) *)
  (* | Failure of string *)
  (*     (\** The prover reports a failure *\) *)
  (* | HighFailure *)
  (*     (\** An error occured during the call to the prover or none *)
  (*         of the given regexps match the output of the prover *\) *)

