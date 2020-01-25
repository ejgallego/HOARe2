(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Common definitions *)
module Util = struct
  module IntSet = Why3.Extset.Make(struct
    type t = int
    let compare = Pervasives.compare
  end)

  module StrSet = Why3.Extset.Make(struct
    type t = string
    let compare = Pervasives.compare
  end)

  (* We reverse the usual order *)
  module RIntMap = Why3.Extmap.Make(struct
    type t = int
    let compare i1 i2 = - (Pervasives.compare i1 i2)
  end)

end

module Options = struct

  (* Components of the compiler *)
  type component =
  | General
  | Lexer
  | Parser
  | TypeChecker
  | Termination
  | SMT
  | Backend

  let default_components =
    (* [Lexer; Parser; TypeChecker] *)
    [Lexer; Parser; TypeChecker; Termination; SMT]
    (* [Lexer; Parser; TypeChecker; Backend] *)

  let components = ref default_components

  let comp_enabled comp =
    List.mem comp !components

  let comp_disable comp =
    let (_, l) = List.partition (fun c -> c = comp) !components in
    components := l

  (* Pretty printing options *)
  type pr_vars =
      PrVarName
    | PrVarNum
    | PrVarIndex
    | PrVarBoth

  type debug_options = {
    components      : component list;
    level           : int;     (* Printing level *)
    unicode         : bool;    (* Use unicode output  *)
    pr_ann          : bool;    (* Print type annotations in the expressions *)
    exp_ann         : bool;    (* Print expression annotations in types *)
    pr_level        : int;     (* Default printing depth *)
    var_output      : pr_vars; (* Ouput names of vars *)
    full_context    : bool;    (* Only names in ctx   *)
    soft_assertions : bool;    (* Don't bail on assertion non-provability *)
  }

  let debug_default = {
    (* components   = [General;Lexer;Parser;TypeChecker;Backend]; *)
    components      = [General;Lexer;Parser;TypeChecker;SMT;Termination;Backend];
    (* components   = [General;Lexer;Parser;SMT;Backend]; *)
    level           = 2;
    unicode         = true;
    pr_ann          = false;
    exp_ann         = false;
    pr_level        = 9;
    var_output      = PrVarName;
    full_context    = true;
    soft_assertions = false;
  }

  let debug_options = ref debug_default

  let debug_comp_disable comp =
    let (_, l) = List.partition (fun c -> c = comp) !debug_options.components in
    debug_options := { !debug_options with components = l }

  let add_why_path path =
    EC.EcProvers.extra_why_path := path :: !EC.EcProvers.extra_why_path

end

module Error = struct

  open Options

  exception Internal of string
  exception Exit of int

  (* Printing levels:
        0  Error
        1  warning
        2  Info
        3+ Debug.

     Debug levels:

     3: Print rules executed and return types.
     4: Print rules executed, return types, constraint store and context.
     5: Print everything, including detailed stuff about type eq and unification, context merging, etc...
     6: Print everything, including optimizations.
  *)

  let comp_to_string = function
    | General     -> "[General  ]"
    | Lexer       -> "[Lexer    ]"
    | Parser      -> "[Parser   ]"
    | TypeChecker -> "[TypeCheck]"
    | Termination -> "[Terminati]"
    | SMT         -> "[SMT      ]"
    | Backend     -> "[Backend  ]"

  let level_to_string = function
    | 0 -> "E "
    | 1 -> "W "
    | 2 -> "I "
    | 3 -> "I+"
    | 4 -> "D1"
    | 5 -> "D2"
    | 6 -> "D3"
    | 7 -> "D4"
    | _ -> ""

  module L = EC.EcLocation

  (* Default print function *)
  let message level component t =
    let loc = L.getloc t in
    if level <= !debug_options.level &&
      List.mem component !debug_options.components then
      (* && not (FileInfo.file_ignored fi) then *)
      begin
        Format.eprintf "@[[%s] %a: @[" (level_to_string level) L.pp_loc loc;
        (* Format.eprintf "@[%s %s %-10s: @[" (level_to_string level) (comp_to_string component) (L.tostring loc); *)
        Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@]@.") Format.err_formatter
      end
    else
      Format.ifprintf Format.err_formatter

(* XXX: Note the caveat that the eprintf here will be executed *)
  let error_msg comp t =
    let loc = L.getloc t in
    let cont _ =
      Format.eprintf "@]@.";
      raise (Exit 1)                in
    Format.eprintf "@[%s %s %s: " (level_to_string 0) (comp_to_string comp) (L.tostring loc);
    Format.kfprintf cont Format.err_formatter

  let error_msg_pp comp t pp v =
    let loc = L.getloc t in
    Format.eprintf "@[%s %s %s: %a@." (level_to_string 0) (comp_to_string comp)
      (L.tostring loc) pp v;
    raise (Exit 1)


  (* Helps with unwanted msg *)
  let supress f = 
    debug_options := {!debug_options with level = !debug_options.level - 1 };
    let x = f () in
    debug_options := {!debug_options with level = !debug_options.level + 1 };
    x

end
