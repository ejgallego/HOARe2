{
  open EcUtils
  open Parser

  module L = EcLocation

  exception LexicalError of L.t option * string

  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let unterminated_string () =
    raise (LexicalError (None, "unterminated string"))

  let _keywords = [                     (* see [keywords.py] *)
    "async"       , ASYNC      ;
    "fun"         , FUN        ;        (* KW: prog *)
    "def"         , DEF        ;        (* KW: prog *)
    "let"         , LET        ;        (* KW: prog *)
    "have"        , HAVE       ;        (* KW: prog *)
    (* "plet"        , PLET       ;        (\* KW: prog *\) *)
    "rec"         , REC        ;
    "mlet"        , MLET       ;        (* KW: prog *)
    "munit"       , MUNIT      ;        (* KW: prog *)
    "clet"        , CLET       ;        (* KW: prog *)
    "cunit"       , CUNIT      ;        (* KW: prog *)
    "in"          , IN         ;        (* KW: prog *)
    "match"       , MATCH      ;        (* KW: prog *)
    "with"        , WITH       ;        (* KW: prog *)
    (* "true"        , TRUE       ;        (\* KW: prog *\) *)
    (* "false"       , FALSE      ;        (\* KW: prog *\) *)
    (* "nil"         , NIL        ;        (\* KW: prog *\) *)
    (* "cons"        , CONS       ;        (\* KW: prog *\) *)
    (* "if"          , IF         ;        (\* KW: prog *\) *)
    (* "then"        , THEN       ;        (\* KW: prog *\) *)
    (* "else"        , ELSE       ;        (\* KW: prog *\) *)
    (* "return"      , RETURN     ;        (\* KW: prog *\) *)
    (* "bool"        , BOOL       ;        (\* KW: prog *\) *)
    (* "int"         , INT        ;        (\* KW: prog *\) *)
    (* "float"       , FLOAT      ;        (\* KW: prog *\) *)
    "struct"      , STRUCT     ;        (* KW: prog *)
    "trust"       , TRUST      ;        (* KW: prog *)
    "M"           , PMONAD     ;        (* KW: prog *)
    "C"           , CMONAD     ;        (* KW: prog *)
    "Pi"          , PI         ;        (* KW: prog *)
    (* "Prop"        , PROP       ;        (\* KW: prog *\) *)
    (* "list"        , LIST       ;        (\* KW: prog *\) *)
    (* "import"      , IMPORT     ;        (\* KW: prog *\) *)
    "open"      , OPEN     ;        (* KW: prog *)
  ]

  let keywords = Hashtbl.create 97

  let _ =
    List.iter
      (fun (x, y) -> Hashtbl.add keywords x y)
      _keywords

  exception InvalidCodePosition

}

let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']
let number  = digit+
let fnumber  = digit+ '.' digit+

let ichar  = (letter | digit | '_' | '\'')
let lident = (lower ichar*) | ('_' ichar+)
let uident = upper ichar*
let tident = '\'' lident
let mident = '&'  (lident | number)

let op_char_1    = ['=' '<' '>']
let op_char_2    = ['+' '-']
let op_char_3_r  = ['*' '%' '\\']
let op_char_3    = op_char_3_r | '/'
(* let op_char_4    = ['$' '&' '?' '@' '^' '|' '#'] *)
let op_char_4    = ['&' '?' '@' '^' '#']
let op_char_34   = op_char_3 | op_char_4
let op_char_234  = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_34_r  = op_char_4 | op_char_3_r
let op_char_234_r = op_char_2 | op_char_34_r

let opdot = ['.']
let op1m = op_char_1234* op_char_1 op_char_1234* opdot?
let op2m = op_char_2 opdot? | op_char_2 op_char_234_r op_char_234* opdot?
let op3m = op_char_34* op_char_3 op_char_34* opdot?
let op4m = op_char_4+ | ("::" ':'+)

let op0  = "\\/" | "/\\" | "=>"
let op1  = op1m | op1m "_" lident
let op2  = op2m | op2m "_" lident
let op3  = op3m | op3m "_" lident
let op4  = op4m | op4m "_" lident

let uniop = '!' | op2

let binop =
  op1 | op2 | op3 | op4 | '+' | '-' |
  "&&" | "/\\" | "||" | "\\/" | "=>" | "<=>" | "=" |
  '>' | '<' | ">=" | "<=" | "<=."


(* -------------------------------------------------------------------- *)
rule main = parse
  | newline      { Lexing.new_line lexbuf; main lexbuf }
  | blank+       { main lexbuf }
  | lident as id { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id { try Hashtbl.find keywords id with Not_found -> UIDENT id }
  | tident       { TIDENT (Lexing.lexeme lexbuf) }
  (* | mident       { MIDENT (Lexing.lexeme lexbuf) } *)
  | number       { NUM  (int_of_string   (Lexing.lexeme lexbuf)) }
  | fnumber      { FNUM (float_of_string (Lexing.lexeme lexbuf)) }
  (* | "<<"         { BACKS } *)
  (* | ">>"         { FWDS } *)

  | "(*" binop "*)" { main lexbuf }
  | '(' blank* (binop as s) blank* ')' { PBINOP s }
  (* | '[' blank* (uniop as s) blank* ']' { PUNIOP (Printf.sprintf "[%s]" s) } *)

  | "(*" { comment lexbuf; main lexbuf }
  (* | "\"" { STRING (Buffer.contents (string (Buffer.create 0) lexbuf)) } *)

  (* boolean operators *)
  (* | '!'   { NOT } *)
  (* | "&&"  { BAND } *)
  (* | "||"  { BOR  } *)

  (* | "&&"  { AND true } *)
  (* | "/\\" { LAND  } *)
  (* | "||"  { LOR } *)
  (* | "\\/" { OR false } *)
  (* | "=>"  { IMPL } *)
  (* | "<=>" { IFF } *)

  (* string symbols *)
  (* | "<-"    { LEFTARROW } *)
  | "->"    { ARROW  }
  (* | ".."    { DOTDOT } *)
  (* | ".["    { DLBRACKET } *)
  (* | ":="    { CEQ } *)
  | "::"    { DCOLON }

  (* | "%r"    { FROM_INT } *)
  (* | "{0,1}" { RBOOL } *)

  (* position *)
  (* | (digit+ ['.' '?'])+ digit+ { *)
  (*     CPOS (oget (cposition_of_string (Lexing.lexeme lexbuf))) *)
  (*   }  *)

  (* punctuation *)
  (* | '_'  { UNDERSCORE } *)
  | '('  { LPAREN }
  | ')'  { RPAREN }
  | '{'  { LBRACE }
  | '}'  { RBRACE }
  | '['  { LBRACKET }
  | ']'  { RBRACKET }
  (* | "<:" { LTCOLON } *)
  | ','  { COMMA }
  (* | ';'  { SEMICOLON } *)
  | ':'  { COLON }
  (* | '?'  { QUESTION } *)
  (* | '%'  { PCENT } *)
  | "*"  { STAR }
  (* | "/"  { SLASH } *)
  (* | "$"  { SAMPLE } *)
  | "|"  { PIPE }
  (* | "`|" { TICKPIPE } *)
  (* | "@"  { AT } *)
  | "$"  { DOLLAR }
  (* | "~"  { TILD } *)

  (* | "==>" { LONGARROW } *)

  (* comparison *)

  (* Needed for let, etc... *)
  | "="  { EQ }
  (* | "<>" { NE } *)

  (* Special cased for the relational variables *)
  | "<1>"  { LEFTVAR  }
  | "<2>"  { RIGHTVAR }

  (* | ">"   { GT } *)
  (* | "<"   { LT } *)
  (* | ">="  { GE } *)
  (* | "<="  { LE } *)

  (* | "-" { MINUS } *)
  (* | "+" { ADD } *)

  (* | "//"  { SLASHSLASH } *)
  (* | "/="  { SLASHEQ } *)
  (* | "//=" { SLASHSLASHEQ } *)

  (* Type annotated *)
  | op0              as s  { OP0 s }
  | op1              as s  { OP1 s }
  | op2              as s  { OP2 s }
  | op3              as s  { OP3 s }
  | op4              as s  { OP4 s }

  (* end of sentence / stream *)
  (* | '.' (eof | blank | newline as r) {  *)
  (*     if r = "\n" then *)
  (*       Lexing.new_line lexbuf; *)
  (*     FINAL *)
  (*   } *)

  | "." { DOT }

  | eof { EOF }

  |  _ as c  { lex_error lexbuf ("illegal character: " ^ String.make 1 c) }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string buf = parse
  | "\""          { buf }
  | "\\n"         { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\r"         { Buffer.add_char buf '\r'; string buf lexbuf }
  | "\\" (_ as c) { Buffer.add_char buf c   ; string buf lexbuf }
  | newline       { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | _ as c        { Buffer.add_char buf c   ; string buf lexbuf }

  | eof           { unterminated_string () }
