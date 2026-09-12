type t =
  (* literals and names *)
  | IDENT of string
  | NUMBER of float
  | STRING of string
  (* keywords *)
  | KW_TYPE
  | KW_FUNCTION
  | KW_IF
  | KW_ELSE
  | KW_LET
  | KW_CONST
  | KW_RETURN
  | KW_TYPEOF
  (* brackets *)
  | LBRACE
  | RBRACE
  | LPAREN
  | RPAREN
  (* separators *)
  | COLON
  | SEMICOLON
  | COMMA
  | DOT
  (* operators *)
  | BAR
  | EQUALS
  | EQ_CHECK
  | NEQ_CHECK
  (* end of input *)
  | EOF

(* A token plus where it came from, for error messages. *)
type located = { token : t; line : int; col : int }

let keywords : (string, t) Hashtbl.t =
  Hashtbl.of_seq
  (List.to_seq
    [
      ("type", KW_TYPE);
      ("function", KW_FUNCTION);
      ("if", KW_IF);
      ("else", KW_ELSE);
      ("let", KW_LET);
      ("const", KW_CONST);
      ("return", KW_RETURN);
      ("typeof", KW_TYPEOF);
  ])

let ident_or_keyword s =
  match Hashtbl.find_opt keywords s with Some kw -> kw | None -> IDENT s

let show = function
  | IDENT s -> Printf.sprintf "identifier %S" s
  | NUMBER n -> Printf.sprintf "number %g" n
  | STRING s -> Printf.sprintf "string %S" s
  | KW_TYPE -> "'type'"
  | KW_FUNCTION -> "'function'"
  | KW_IF -> "'if'"
  | KW_ELSE -> "'else'"
  | KW_LET -> "'let'"
  | KW_CONST -> "'const'"
  | KW_RETURN -> "'return'"
  | KW_TYPEOF -> "'typeof'"
  | LBRACE -> "'{'"
  | RBRACE -> "'}'"
  | LPAREN -> "'('"
  | RPAREN -> "')'"
  | COLON -> "':'"
  | SEMICOLON -> "';'"
  | COMMA -> "','"
  | DOT -> "'.'"
  | BAR -> "'|'"
  | EQUALS -> "'='"
  | EQ_CHECK -> "'==='"
  | NEQ_CHECK -> "'!=='"
  | EOF -> "end of input"
