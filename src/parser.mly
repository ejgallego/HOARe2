(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   Copyright (c) 2015, CRI-MINES ParisTech/PSL Research University

   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

%{
  open EC.Utils
  open EC.Location
  open Parsetree

  module E  = Exp
  module EB = E.Builders
  module C  = Constants

  let error loc msg = raise (ParseError (loc, msg))

  (* Binary app with an infix operation *)
  let mk_app env op e1 e2 =
    let op_name = "infix " ^ op.pl_desc                        in
    let e_op    = EB.resolve_ident env op.pl_loc op_name None  in
    mk_loc e1.pl_loc @@ EApp(e_op, [e1;e2])

  (* let pqsymb_of_symb loc x : pqsymbol = *)
  (*   mk_loc loc ([], x) *)

  (* Native @@ is already in ocaml 4.0 *)
  let (@@) x y = x y

  (* Extend  *)
  let rec extend_from_pat env bl = match bl with
    | []                      -> ([], env)
    | (bid, brel, bty) :: rbl -> let (bi,  b_env)   = Env.extend bid.pl_desc brel true bty env in
                                 let (bil, bil_env) = extend_from_pat b_env rbl                in
                                 (bi :: bil, bil_env)


  (* The unit type is useful *)
  let lookup_type env loc ty =
    let (th, _) =
      try Env.lookup_type env ty
      with Not_found -> error loc (Some (ty ^ "not found"))
    in (th, ty)

  let unit_type env loc =
    mk_loc loc (TPrim (lookup_type env loc "tuple0", []), None)

  (* Helper for the multiple arguments syntactic sugar *)
  let process_binder_list bl env =
    let (arg_list, b_env) = List.fold_left (
      fun (l, env) ann_bi ->
        let (aid, arel, aty) = ann_bi env                               in
        let (b_a, b_env)     = Env.extend aid.pl_desc arel true aty env in
        ((b_a, aid.pl_loc, aty) :: l, b_env)
    ) ([], env) bl                                                      in
    (List.rev arg_list, b_env)

  let rec pi_from_arglist al rty = match al with
    | []                 -> rty
    | (b, loc, ty) :: ts -> mk_loc loc (TPi (b, ty, pi_from_arglist ts rty), None)

  let rec fun_from_arglist al e = match al with
    | []                 -> e
    | (b, loc, ty) :: ts -> mk_loc loc @@ ELam (b, ty, fun_from_arglist ts e)

%}

%token <string> LIDENT
%token <string> UIDENT
%token <string> TIDENT

%token <string> PBINOP

%token <int>    NUM
%token <float>  FNUM
(* %token <string> STRING *)

(* Tokens *)

(* %token LAND *)
(* %token LOR *)
(* %token BAND *)
(* %token BOR *)

(* %token ADD *)
(* %token ADMIT *)
(* %token ALIAS *)
(* %token APPLY *)
%token ARROW
%token ASYNC
(* %token AS *)
(* %token ASSERT *)
(* %token ASSUMPTION *)
(* %token AT *)
(* %token AUTO *)
(* %token AXIOM *)
(* %token BETA *)
(* %token BOOL *)
(* %token BY *)
(* %token BYPR *)
(* %token CALL *)
(* %token CASE *)
(* %token CEQ *)
(* %token CFOLD *)
(* %token CHANGE *)
(* %token CHECKPROOF *)
(* %token CLAIM *)
(* %token CLASS *)
(* %token CLEAR *)
(* %token CLONE *)
%token CLET
%token COLON
%token COMMA
%token CUNIT
(* %token COMPUTE *)
(* %token CONGR *)
(* %token CONS *)
(* %token CONSEQ *)
(* %token EXFALSO *)
(* %token CONST *)
(* %token CUT *)
(* %token DATATYPE *)
%token DCOLON
(* %token DEBUG *)
(* %token DECLARE *)
(* %token DELTA *)
(* %token DLBRACKET *)
%token DEF
(* %token DO *)
%token DOLLAR
%token DOT
(* %token DOTDOT *)
(* %token DROP *)
(* %token ELIM *)
(* %token ELIMT *)
(* %token ELSE *)
(* %token END *)
%token EOF
%token EQ
(* %token EQUIV *)
(* %token EQUIVDENO *)
(* %token EXIST *)
(* %token EXPORT *)
(* %token FEL *)
(* %token FIELD *)
(* %token RING *)
(* %token FALSE *)
(* %token FINAL *)
(* %token FIRST *)
(* %token FISSION *)
(* %token FORALL *)
(* %token FLOAT *)
(* %token FROM_INT *)
%token FUN
(* %token FUSION *)
(* %token FWDS *)
(* %token GENERALIZE  *)
(* %token GLOB *)
%token HAVE
(* %token HOARE *)
(* %token IDTAC *)
(* %token IF *)
(* %token IFF *)
(* %token IMPL *)
(* %token IMPORT *)
(* %token IMPOSSIBLE *)
%token IN
(* %token INLINE *)
(* %token INSTANCE *)
(* %token INT *)
(* %token INTROS *)
(* %token IOTA *)
(* %token KILL *)
(* %token LAST *)
%token LBRACE
%token LBRACKET
(* %token LEFT *)
(* %token LEFTARROW *)
(* %token LEMMA *)
%token LET
(* %token LIST *)
(* %token LOCAL *)
(* %token LOGIC *)
(* %token LONGARROW *)
(* %token LOSSLESS *)
%token LPAREN
(* %token LPRIM *)
%token MATCH

(* %token MINUS *)
%token MLET
(* %token MODPATH *)
(* %token MODULE *)
%token PMONAD
%token CMONAD
%token MUNIT
(* %token NE *)
(* %token NIL *)
(* %token NOSMT *)
(* %token NOT *)
(* %token OF *)
(* %token OFF *)
(* %token ON *)
(* %token OP *)
%token OPEN
(* %token PCENT *)
(* %token PLET *)
%token PI
%token PIPE
(* %token POSE *)
(* %token PR *)
(* %token PRAGMA *)
(* %token PRBOUNDED *)
(* %token PRED *)
(* %token PRFALSE *)
(* %token PRIM *)
(* %token PRINT *)
(* %token PROGRESS *)
(* %token PROP *)
(* %token PROOF *)
(* %token PROVER *)
(* %token QED *)
(* %token QUESTION *)
(* %token RBOOL *)
%token RBRACE
%token RBRACKET
(* %token RCONDF *)
(* %token RCONDT *)
(* %token REALIZE *)
(* %token REFLEX *)
(* %token REQUIRE *)
%token REC
(* %token RES *)
(* %token RETURN *)
(* %token REWRITE *)
(* %token RIGHT *)
(* %token RND *)
%token RPAREN
(* %token SAME *)
(* %token SAMPLE *)
(* %token SAVE *)
(* %token SECTION *)
(* %token SELF *)
(* %token SEMICOLON *)
(* %token SEQ *)
(* %token SIMPLIFY *)
(* %token SKIP *)
(* %token SLASH *)
(* %token SLASHEQ *)
(* %token SLASHSLASH *)
(* %token SLASHSLASHEQ *)
(* %token SMT *)
(* %token SP *)
(* %token SPLIT *)
(* %token SPLITWHILE *)
%token STAR
(* %token STRICT *)
%token STRUCT
(* %token SUBST *)
(* %token SWAP *)
(* %token THEN *)
(* %token THEORY *)
(* %token TICKPIPE *)
(* %token TILD *)
(* %token TIMEOUT *)
(* %token TRIVIAL *)
(* %token TRY *)
(* %token TRUE *)
%token TRUST
(* %token TYPE *)
(* %token UNDERSCORE *)
(* %token UNDO *)
(* %token UNROLL *)
(* %token USING *)
(* %token VAR *)
(* %token WHILE *)
(* %token WHY3 *)
%token WITH
(* %token WP *)
(* %token EQOBSIN *)
(* %token TRANSITIVITY *)
(* %token SYMMETRY *)
(* %token ZETA  *)
(* %token EAGER *)

%token <string> OP0 OP1 OP2 OP3 OP4
(* %token LTCOLON GT LT GE LE *)
%token GT LT

(* Left and right variables *)
%token LEFTVAR RIGHTVAR


(* %nonassoc prec_below_comma *)
(* %nonassoc COMMA ELSE *)

(* XXXX: Is this right? *)
(* %nonassoc IN *)
(* %nonassoc prec_below_IMPL *)
(* %right    IMPL *)
(* %nonassoc IFF *)
(* %right    OR *)
(* %right    AND *)
(* %right    LOR *)
(* %right    LAND *)
(* %nonassoc NOT *)

%nonassoc EQ

(* %nonassoc prec_below_order *)

%right OP0 DOLLAR
%left OP1 GT LT
%left OP2
(* XXX: Is this right? *)
(* %right ARROW *)
%left OP3 STAR
%left OP4
(* %left OP4 DCOLON *)

(* XXX: Is this right? *)
(* %nonassoc LBRACE *)

(* %right STAR *)

(* %right SEMICOLON *)

(* %nonassoc prec_tactic *)

%type <Parsetree.exp> body

%start body
%%

(* -------------------------------------------------------------------- *)
%inline lident: x=loc(LIDENT) { x };
%inline uident: x=loc(UIDENT) { x };

%inline _ident:
| x=LIDENT { x }
| x=UIDENT { x }
;

%inline ident:
| x=loc(_ident) { x }
;

(*
%inline number: n=NUM { n };
*)

(* -------------------------------------------------------------------- *)
%inline _oident:
| x=LIDENT { x }
| x=UIDENT { x }
(* | x=PUNIOP { x } *)
(* | x=paren(PUNIOP) { x } *)
| x=PBINOP { x }

(* EG: This may be very useful but not for now *)

(* | paren(DCOLON) { EcCoreLib.s_cons } *)

(* | x=loc(STRING) { *)
(*     if not (EcCoreLib.is_mixfix_op (unloc x)) then *)
(*       error x.pl_loc (Some "invalid mixfix operator"); *)
(*     unloc x *)
(*   } *)
;

%inline oident:
| x=loc(_oident) { x }
;

(* -------------------------------------------------------------------- *)
(* Expressions                                                          *)

trust_form:
| LET                  { None }
| TRUST s=paren(ident) { Some s.pl_desc }

let_form:
| trust_form      { ($1, true ) }
| trust_form DEF  { ($1, false) }

body:
  exp EOF { $1 (E.ExpState.fo_init ()) }

exp:
| p=loc(OPEN) tfile=LIDENT DOT tname=UIDENT IN e=exp
   { fun env ->
     (* Should be Why3.load_theory *)
     let th      = (tfile, tname)                     in
     let th_env  = WhyImport.load_why3_theory th env  in

     mk_loc p.pl_loc @@ EImport (th, e th_env)
   }

(* Let *)
| trust=let_form id=oident arg_l=list(paren(ann_binder)) rel=bsymbol r_ty=ty EQ iexp=exp IN oexp=exp
   { fun env ->
     (* Types *)
     let (trust, opaque)   = trust                                  in
     let (arg_list, b_env) = process_binder_list arg_l env          in
     let r_ty              = r_ty b_env                             in

     (* We must now introduce as many lambdas as arguments *)
     let iexp              = fun_from_arglist arg_list (iexp b_env) in

     (* Ty is the type for the let *)
     let ty                = pi_from_arglist arg_list r_ty          in

     (* Now we extend the environment for oexp *)
     let (bi, n_env)       = Env.extend id.pl_desc rel opaque ty env in

     mk_loc (EC.Location.make $startpos $endpos) @@
       ELet (bi, trust, ty, iexp, oexp n_env)
   }

(* Sugar for let k : { _ : () | phi } = () in e *)
| HAVE h=loc(COLON) form=brace(exp) IN oexp=exp
   { fun env ->
     (* Types *)

     let trust, opaque, rel = None, true, false                                        in

     (* Unit assertion *)
     let unit_ty       = unit_type env h.pl_loc                                        in
     let (u_bi, u_env) = Env.extend "_" rel opaque unit_ty env                         in

     (* The expression is under the context of () *)
     let cut_ty  = mk_loc h.pl_loc @@ (TRef(u_bi, unit_ty, form u_env), None)          in
     let exp_unit  = mk_loc h.pl_loc C.exp_unit                                        in

     (* Now we extend the environment with the formula *)
     let (bi, n_env)       = Env.extend "kut" rel opaque cut_ty env                    in

     mk_loc (EC.Location.make $startpos $endpos) @@
       ELet (bi, trust, cut_ty, exp_unit, oexp n_env)
   }


(* This is slightly duplicated from the above, could surely use some
   refactoring *)
| LET REC fid=oident arg_l=nonempty_list(paren(ann_binder)) tc=term_ann rel=bsymbol r_ty=ty  EQ iexp=exp IN oexp=exp
   { fun env ->

     let opaque = true                                                        in

     (* Check that argument list is free of f *)
     let (arg_list, b_env) = process_binder_list arg_l env                    in
     let n_args = List.length arg_list                                        in

     (* Ty is the type of the fixpoint *)
     let r_ty              = r_ty b_env                                       in
     let ty                = pi_from_arglist arg_list r_ty                    in

     (* Termination annotation *)
     let tc     = tc n_args b_env                                             in

     (* Now introduce f *)
     let (bf, fix_env)   = Env.extend fid.pl_desc rel opaque ty env           in

     (* Generate the lambas *)
     let (fix_alist, fix_b_env) = process_binder_list arg_l fix_env           in

     (* We must now introduce as many lambdas as arguments *)
     let iexp                   = fun_from_arglist fix_alist (iexp fix_b_env) in

     let fix_exp = mk_loc (EC.Location.make $startpos $endpos) @@
       EFix (bf, ty, tc, iexp) in

     mk_loc (EC.Location.make $startpos $endpos) @@
       ELet (bf, None, ty, fix_exp, oexp fix_env)
   }

| mt=munit e=exp
   { fun env ->
     mk_loc (EC.Location.make $startpos $endpos) @@
       EMUnit (mt, e env)
   }

| mt=mlet lb=binder EQ iexp=exp IN ty_ann=option(brackets(ty)) oexp=exp
   { fun env ->
       let (id, rel, ty) = lb env                                  in
       let (bi, n_env)   = Env.extend id.pl_desc rel true ty env   in
       let ty_ann        = Option.map (fun f -> f env) ty_ann      in
       mk_loc (EC.Location.make $startpos $endpos) @@
         EMLet (mt, bi, ty_ann, iexp env, oexp n_env)
   }

| asyn=async_ann l=loc(MATCH) e_m=op_exp WITH t_m=brackets(ty) pats=lmatchcase
   { fun env ->
     mk_loc l.pl_loc @@
       EMatch (asyn, e_m env, pats env, Some (t_m env))
   }

(*
| l=loc(FUN) lb=paren(ann_binder) ARROW ie=exp
   { fun env ->
       let (aid, arel, aty) = lb env                                    in
       let (ba, a_env)      = Env.extend aid.pl_desc arel aty env       in
       mk_loc l.pl_loc
	 (ELam (ba, aty, ie a_env))
   }
*)
| _l=loc(FUN) ab=nonempty_list(paren(ann_binder)) ARROW ie=exp
   { fun env ->
     (* We must fold the environment first *)
     let (arg_list, b_env) = process_binder_list ab env in
     fun_from_arglist arg_list (ie b_env)
   }

| e=op_exp { e }
;

(* Termination annotation *)
term_ann :
|                                       (*  *)
  { fun _ _ -> None }

| loc(LBRACE) STRUCT l=oident RBRACE
  { fun n_args env ->

    match Env.lookup l.pl_desc env with
    (* Adjust the argument number *)
    | Some (idx, _, _) -> Some ((n_args - idx - 1), n_args)
    | None -> error l.pl_loc (Some ("Identifier " ^ l.pl_desc ^ " not found"))
  }

async_ann:
|       { false; }
| ASYNC { true;  }

munit:
| MUNIT { PMonad }
| CUNIT { CMonad }

mlet:
| MLET { PMonad }
| CLET { CMonad }

(* FIXME: Use nonempty_list(pattern) *)
(* Non-empty Patterns *)
lmatchcase:
| p=matchcase
   {
     fun env ->
       [p env]
   }

| p=matchcase pl=lmatchcase
   { fun env ->
     (p env) :: (pl env)
   }

matchcase:
| PIPE pat=pattern ARROW pe=exp
   {
     fun env ->
       let (cs, bl)     = pat env                                              in
       let (bil, p_env) = extend_from_pat env bl                               in
       let lpat         = mk_loc (EC.Location.make $startpos $endpos) (cs, bil) in
       (lpat, pe p_env)
   }

pattern:
| cs=constructor bl=list(binder)
    {
      fun env ->
        let bl = List.map (fun e -> e env) bl                                  in
        (cs env, bl)
    }

(* Tuples *)
| elems=paren(plist2(binder, COMMA))
   {
     fun env ->
       let elems = List.map (fun e -> e env) elems                             in
       let n     = List.length elems                                           in
       ((C.tuple_th n, C.cs_tuple_name n), elems)
   }

constructor:
| cs=uident
    { fun env ->
          try
            let th, _ty = Env.lookup_cons env cs.pl_desc                       in
            (th, cs.pl_desc)
          with Not_found -> error cs.pl_loc (Some (cs.pl_desc ^ " not found"))
    }


(* PIPE CONS LPAREN xb=ann_binder COMMA lb=ann_binder RPAREN ARROW re=exp *)
       (* let (xid, xrel, xty) = xb env                                    in *)
       (* let (lid, lrel, lty) = lb env                                    in *)
       (* let (bx, x_env)      = Env.extend xid.pl_desc xrel xty env       in *)
       (* let (bl, l_env)      = Env.extend lid.pl_desc lrel lty x_env     in *)
       (* mk_loc (EcLocation.make $startpos $endpos) *)
       (*   (EMatch (e_m env, (t_m env, false), le env, bx, (xty, false), bl, (lty, false), re l_env)) *)

(* Binary operators *)
op_exp:
| f=op_exp DOLLAR e=op_exp
   { fun env ->
     let e' = e env in
     mk_loc e'.pl_loc (EApp (f env, [e']))
   }
| e1=op_exp op=loc(OP0) e2=op_exp
   { fun env ->
     (* Printf.printf "op4 : %s\n" op.pl_desc; *)
     mk_app env op (e1 env) (e2 env)
   }
| r=op1_exp
   { r }

op1_exp:

| e1=op1_exp op=loc(OP1) e2=op1_exp
   { fun env ->
     (* Printf.printf "op3 : %s\n" op.pl_desc; *)
     mk_app env op (e1 env) (e2 env)
   }
| e1=op1_exp op=loc(LT) e2=op1_exp
   { fun env ->
     (* Printf.printf "op3 : <\n"; *)
     mk_app env (mk_loc op.pl_loc "<") (e1 env) (e2 env)
   }
| e1=op1_exp op=loc(GT) e2=op1_exp
   { fun env ->
     (* Printf.printf "op3 : >\n"; *)
     mk_app env (mk_loc op.pl_loc ">") (e1 env) (e2 env)
   }
| e1=op1_exp op=loc(EQ) e2=op1_exp
   { fun env ->
     (* Printf.printf "op1 : =\n"; *)
     mk_app env (mk_loc op.pl_loc "=") (e1 env) (e2 env)
   }
| r=op2_exp
   { r }

op2_exp:
| e1=op2_exp op=loc(STAR) e2=op2_exp
   { fun env ->
     (* Printf.printf "op2 : *\n"; *)
     mk_app env (mk_loc op.pl_loc "*") (e1 env) (e2 env)
   }
| e1=op2_exp op=loc(OP2) e2=op2_exp
   { fun env ->
     (* Printf.printf "op2 : %s\n" op.pl_desc; *)
     mk_app env op (e1 env) (e2 env)
   }
| r=op3_exp
   { r }

op3_exp:
| e1=op3_exp op=loc(OP3) e2=op3_exp
   { fun env ->
     (* Printf.printf "op1 : %s\n" op.pl_desc; *)
     mk_app env op (e1 env) (e2 env)
   }
| r=op4_exp
   { r }

op4_exp:
| e1=op4_exp op=loc(OP4) e2=op4_exp
   { fun env ->
     (* Printf.printf "op4 : %s\n" op.pl_desc; *)
     mk_app env op (e1 env) (e2 env)
   }
| fe=fexp
   { fe }

(* Weird *)
(* op_exp: *)
(* | e1=op_exp op=loc(OP4) e2=op_exp *)
(*    { fun env -> *)
(*      Printf.printf "op4 : %s\n" op.pl_desc; *)
(*      mk_app env op (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(OP3) e2=op_exp *)
(*    { fun env -> *)
(*      Printf.printf "op3 : %s\n" op.pl_desc; *)
(*      mk_app env op (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(LT) e2=op_exp *)
(*    { fun env -> *)
(*      mk_app env (mk_loc op.pl_loc "<") (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(GT) e2=op_exp *)
(*    { fun env -> *)
(*      mk_app env (mk_loc op.pl_loc ">") (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(STAR) e2=op_exp *)
(*    { fun env -> *)
(*      mk_app env (mk_loc op.pl_loc "*") (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(OP2) e2=op_exp *)
(*    { fun env -> *)
(*      Printf.printf "op2 : %s\n" op.pl_desc; *)
(*      mk_app env op (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(OP1) e2=op_exp *)
(*    { fun env -> *)
(*      Printf.printf "op1 : %s\n" op.pl_desc; *)
(*      mk_app env op (e1 env) (e2 env) *)
(*    } *)
(* | e1=op_exp op=loc(EQ) e2=op_exp *)
(*    { fun env -> *)
(*      mk_app env (mk_loc op.pl_loc "=") (e1 env) (e2 env) *)
(*    } *)
(* | fe=fexp *)
(*    { fe } *)

fexp:
| e=aexp        { e }
| f=fexp e=aexp { fun env ->
                      let e' = e env in
                      mk_loc e'.pl_loc (EApp (f env, [e']))
		}

varside:
| LEFTVAR  { SiLeft  }
| RIGHTVAR { SiRight }

aexp:
(* Regular identifier [lowercase] *)
| id=lident     { fun env ->
                      EB.resolve_ident env id.pl_loc id.pl_desc None
		}
| rid=lident s=varside
                { fun env ->
                      EB.resolve_ident env rid.pl_loc rid.pl_desc (Some s)
		}
| cid=constructor
                { fun env ->
                      let cs = cid env in
                      mk_loc (EC.Location.make $startpos $endpos) (ECs cs)
                }

| l=loc(LPAREN) RPAREN { fun _ ->
                         mk_loc l.pl_loc (C.exp_unit)
		       }
| n=loc(NUM)    { fun _ ->
                      mk_loc n.pl_loc (C.exp_int n.pl_desc)
                }
| f=loc(FNUM)   { fun _ ->
                      mk_loc f.pl_loc (C.exp_float f.pl_desc)
                }
(* Kinda hacky *)
| elems=loc(paren(plist2(op_exp, COMMA)))
   { fun env ->
     let args  = List.map (fun e -> e env) elems.pl_desc in
     let arity = List.length args                        in
     EB.mk_exp_tuple elems.pl_loc arity args
   }

(* | n=loc(TRUE)    { fun _ -> *)
(*                       mk_loc n.pl_loc (EConst (ECBool true)) *)
(*                  } *)
(* | n=loc(FALSE)    { fun _ -> *)
(*                       mk_loc n.pl_loc (EConst (ECBool false)) *)
(*                  } *)
(* | NIL LBRACKET t=ty RBRACKET *)
(*    { fun env -> *)
(*      mk_loc (EC.Location.make $startpos $endpos) @@ *)
(*        ENil (t env) *)
(*    } *)
(* | CONS LPAREN e1=exp COMMA e2=exp RPAREN *)
(*    { fun env -> *)
(*      mk_loc (EC.Location.make $startpos $endpos) @@ *)
(*        ECons (e1 env, e2 env) *)
(*    } *)
(* | LPAREN e1=exp COMMA e2=exp RPAREN *)
(*    { fun env -> *)
(*      mk_loc (EC.Location.make $startpos $endpos) @@ *)
(*        EPair (e1 env, e2 env) *)
(*    } *)
| e=paren(exp) { e }

bsymbol:
| COLON  { false }
| DCOLON { true  }

(* Binder without annotation *)
binder:
| id=oident
   { fun env ->
     (* Little bit of a hack *)
     let ty = unit_type env id.pl_loc in
     (id, true, ty)
   }

(* Binder with annotation *)
ann_binder:
| id=oident rel=bsymbol t=ty
   { fun env ->
     (id, rel, t env)
   }


(* Inductive types *)
ty:

| ty_qv=TIDENT
    { fun _env ->
      mk_loc (EC.Location.make $startpos $endpos) @@
        (TQVar ty_qv, None)
    }

(* Type application *)
| ty_cs=lident ty_args=list(ty)
   { fun env ->
     let ty_cons = lookup_type env ty_cs.pl_loc ty_cs.pl_desc in
     mk_loc (EC.Location.make $startpos $endpos) @@
       (TPrim (ty_cons, List.map (fun f -> f env) ty_args), None)
   }

(* Tuples *)
| p1=loc(LPAREN) RPAREN { fun env -> unit_type env p1.pl_loc }
| args=paren(plist2(ty, STAR))
    {
      fun env ->
        let args = List.map (fun x -> x env) args in
        mk_loc (EC.Location.make $startpos $endpos) @@ (C.ty_tuple args, None)
    }

(* Parenthesis *)
| m=paren(ty) { m }

(* Monad *)
| m=loc(CMONAD) t=ty
   { fun env ->
     mk_loc m.pl_loc (TC (t env), None)
   }

(* Version without alpha and delta *)
| m=loc(PMONAD) t=ty
   { fun env ->
     let zero = mk_loc m.pl_loc @@ EConst (ECReal 0.0) in
     mk_loc m.pl_loc (TM(zero, zero, t env), None)
   }

(* Version without delta *)
| m=loc(PMONAD) a=brackets(exp) t=ty
   { fun env ->
     let zero = mk_loc m.pl_loc @@ EConst (ECReal 0.0) in
     mk_loc m.pl_loc (TM(a env, zero, t env), None)
   }

| m=loc(PMONAD) LBRACKET a=exp COMMA d=exp RBRACKET t=ty
   { fun env ->
     mk_loc m.pl_loc (TM(a env, d env, t env), None)
   }

(* | m=loc(PMONAD) LBRACKET a=ident COMMA d=ident RBRACKET t=ty *)
(*    { fun env -> *)
(*      let vtype            = mk_loc a.pl_loc (EC.ty_float, None)     in *)
(*      let (ab, a_env)      = Env.extend a.pl_desc false vtype   env in *)
(*      let (db, d_env)      = Env.extend d.pl_desc false vtype a_env in *)
(*      mk_loc m.pl_loc (TM(ab, db, t d_env), None) *)
(*    } *)

(* Support a list of binders *)
| PI ab=nonempty_list(paren(ann_binder)) DOT rty=ty
   { fun env ->
     (* We must fold the environment first *)
     let (arg_list, b_env) = process_binder_list ab env in
     pi_from_arglist arg_list (rty b_env)
   }

| LBRACE rb=ann_binder PIPE ass=exp RBRACE
   { fun env ->
     let (rid, rrel, rty) = rb env                                   in
     let (br, r_env)      = Env.extend rid.pl_desc rrel true rty env in
     mk_loc rid.pl_loc (TRef(br, rty, ass r_env), None)
   }

(* form: *)
(* | e1=exp pred=lpred e2=exp *)
(*   { fun env -> *)
(*         mk_loc pred.pl_loc (FPred(pred.pl_desc, (e1 env), (e2 env))) *)
(*   } *)
(* | f1=form op=lop f2=form *)
(*   { fun env -> *)
(*         mk_loc op.pl_loc (FBinOp(op.pl_desc, (f1 env), (f2 env))) *)
(*   } *)
(* | f=paren(form) *)
(*   { f } *)

(* lpred: *)
(* | o=loc(EQ) *)
(*   { mk_loc o.pl_loc PredLe } *)
(* | o=loc(LE) *)
(*   { mk_loc o.pl_loc PredEq } *)

(* lop: *)
(* | o=loc(LAND) *)
(*   { mk_loc o.pl_loc BiOpAnd } *)
(* | o=loc(LOR) *)
(*   { mk_loc o.pl_loc BiOpAnd } *)

(* -------------------------------------------------------------------- *)
(* Will be useful                                                       *)

%inline plist0(X, S):
| aout=separated_list(S, X) { aout }
;

iplist1_r(X, S):
| x=X { [x] }
| xs=iplist1_r(X, S) S x=X { x :: xs }
;

%inline iplist1(X, S):
| xs=iplist1_r(X, S) { List.rev xs }
;

%inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }
;

%inline plist2(X, S):
| x=X S xs=plist1(X, S) { x :: xs }
;

%inline list2(X):
| x=X xs=X+ { x :: xs }
;

(*
%inline empty:
| /**/ { () }
;
*)
(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }
;

%inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }
;

%inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }
;

(* -------------------------------------------------------------------- *)
%inline paren(X):
| LPAREN x=X RPAREN { x }
;

%inline brace(X):
| LBRACE x=X RBRACE { x }
;

%inline brackets(X):
| LBRACKET x=X RBRACKET { x }
;

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EC.Location.make $startpos $endpos;
    }
  }
;
