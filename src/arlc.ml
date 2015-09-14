(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Unix

open Env
open EcIo

(* open Eval *)

open Support.Options
open Support.Error

module L = EcLocation
module P = Print

let outfile    = ref (None : string option)
let infile     = ref ("" : string)

let argDefs = [
  "-v",                Arg.Int  (fun l  -> debug_options := {!debug_options with level = l} ),       "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;

  "-L",                Arg.String add_why_path,  "Add include path for why3" ;

  "--timeout",         Arg.Int  (fun tl -> ArlcSolver.tlimit := tl ),  "Set timeout for the solvers" ;

  "--disable-types",   Arg.Unit (fun () -> comp_disable TypeChecker ), "Disable type checking" ;
  "--disable-tc",      Arg.Unit (fun () -> comp_disable Termination ), "Disable termination checking" ;
  "--disable-smt",     Arg.Unit (fun () -> comp_disable SMT ),         "Disable SMT" ;
  "--vc-info",         Arg.Unit (fun () -> debug_comp_disable TypeChecker), "Print info about VC only" ;

  "--disable-unicode", Arg.Unit (fun () -> debug_options := {!debug_options with unicode = false} ), "Disable unicode printing" ;
  "--soft-assertions", Arg.Unit (fun () -> debug_options := {!debug_options with soft_assertions = true} ), "Don't bail on false or non-provable assertions" ;
  "--enable-annot",    Arg.Unit (fun () -> debug_options := {!debug_options with pr_ann  = true} ),  "Enable printing of type annotations" ;
  "--enable-exp-annot",Arg.Unit (fun () -> debug_options := {!debug_options with exp_ann  = true} ),  "Enable printing of expression annotations" ;
  "--print-var-full",  Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarBoth} ), "Print names and indexes of variables" ;
  "--print-var-index", Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarIndex}), "Print just indexes of variables" ;
  "--print-var-num", Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarNum}), "Prints a generated name from the index, very useful when user names are ambiguous" ;
]

let loci loc = L.mk_loc loc ()
let dp       = loci L._dummy
let main_error = error_msg General

let main_warning fi = message 1 General fi
let main_info    fi = message 2 General fi
let main_info2   fi = message 3 General fi
let main_debug   fi = message 4 General fi

let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> main_error dp "You must specify exactly one input file"
       | None -> inFile := Some(s))
     "Usage: arlc [options] inputfile";
  match !inFile with
      None    -> main_error dp "No input file specified (use --help to display usage info)"; ""
    | Some(s) -> s

(* Parse the input *)
let parse file =
  let reader  = EcIo.from_file file in
  let program =
    try EcIo.parse reader
    with
    | Parsetree.ParseError(loc, msg) -> error_msg Parser (loci loc) "%s" (EcUtils.odfl "Unknown error" msg)
    | Parser.Error                   -> error_msg Parser (loci (EcLocation.of_lexbuf (lexbuf reader))) "Parse Error"
  in
  program

let type_check file program =
  let ty = Ty_ref.get_type file program  in
  main_warning dp "Type of the program: @[%a@]" P.pp_ty ty;
  (* main_warning dp "NF Type            : @[%a@]" Print.pp_ty (Assertion.ty_norm Exp.ExpState.empty ty); *)
  main_debug   dp "Trivial VCs  : %d"               !Assertion.trivial_assertions;
  main_warning dp "Number of VCs: %d"               !Assertion.total_assertions;
  main_warning dp "%d failed assertions: [@[<v>%a@]]" (List.length !Assertion.failed_assertions) (P.pp_list_sep ";" P.pp_exp) !Assertion.failed_assertions;
  main_warning dp "Pending VC: [@[<v>%a@]]"      (P.pp_list P.pp_str) !Assertion.pending_vc
(*   check_main_type ty *)

(* At some point we must use this *)
let get_tty_size = ()

(* === The main function === *)
let main () =

  (* Setup the pretty printing engine *)
  let fmt_margin =
    try
      snd (Util.get_terminal_size ())
    with _ ->
      main_warning dp "Failed to get terminal size value.";
      140
  in

  let set_pp fmt =
    Format.pp_set_ellipsis_text fmt "[...]";
    Format.pp_set_margin fmt (fmt_margin + 1); (* Don't ever ask *)
    Format.pp_set_max_indent fmt fmt_margin    in

  set_pp Format.std_formatter;
  set_pp Format.err_formatter;

  (* Read the command-line arguments *)
  infile  := parseArgs();

  main_info dp "Effective list of SMT to be used: @[%a@]"
            (Print.pp_list_sep "," Print.pp_str) (ArlcSolver.solvers ());

  let program    = parse !infile                   in
  let pname      = Filename.chop_extension !infile in

  (* Print the results of the parsing phase *)
  (* let program = Parsetree.exp_uncurry program in *)

  main_debug dp "Parsing completed!";
  main_info2 dp "Parsed program:@\n@[%a@]@." Print.pp_exp program;

  if comp_enabled TypeChecker then
    type_check pname program;

  (* let e = nstep 2 program in *)
  (* main_debug dp "Execution:@\n@[%a@]@." Print.pp_exp e; *)
  ()
(* === Call the main function and catch any exceptions === *)

let res =
  try main ();
      0
  with Exit x -> x
let () = exit res
