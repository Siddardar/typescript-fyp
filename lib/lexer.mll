{
  exception Error of string

  let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
}

let blank  = [' ' '\t' '\r']+
let digit  = ['0'-'9']
let number = digit+ ('.' digit+)?
let ident  = ['a'-'z' 'A'-'Z' '_' '$'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '$']*

(* TODO: newlines can also be separators for fields in objects *)
rule read = parse
  | blank        { read lexbuf }
  | '\n'         { Lexing.new_line lexbuf; read lexbuf }

  (* comments *)
  | "//"         { line_comment lexbuf }
  | "/*"         { block_comment lexbuf }

  (* literals and names; Token.ident_or_keyword turns keywords into their own tokens *)
  | number as s  { Token.NUMBER (float_of_string s) }
  | ident as s   { Token.ident_or_keyword s }
  | '"'          { string_literal (Buffer.create 16) lexbuf }

  (* multi-character operators *)
  | "==="        { Token.EQ_CHECK }
  | "!=="        { Token.NEQ_CHECK }

  (* brackets *)
  | '{'          { Token.LBRACE }
  | '}'          { Token.RBRACE }
  | '('          { Token.LPAREN }
  | ')'          { Token.RPAREN }

  (* separators *)
  | ':'          { Token.COLON }
  | ';'          { Token.SEMICOLON }
  | ','          { Token.COMMA }
  | '.'          { Token.DOT }

  (* operators *)
  | '|'          { Token.BAR }
  | '='          { Token.EQUALS }

  | eof          { Token.EOF }
  | _ as c       { error "unexpected character %C" c }

(* Everything to the end of the line, then carry on. *)
and line_comment = parse
  | '\n'         { Lexing.new_line lexbuf; read lexbuf }
  | eof          { Token.EOF }
  | _            { line_comment lexbuf }

and block_comment = parse
  | "*/"         { read lexbuf }
  | '\n'         { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof          { error "unterminated comment" }
  | _            { block_comment lexbuf }

(* Accumulates the unescaped contents, so a single regex will not do. *)
and string_literal buf = parse
  | '"'          { Token.STRING (Buffer.contents buf) }
  | "\\\""       { Buffer.add_char buf '"';  string_literal buf lexbuf }
  | "\\\\"       { Buffer.add_char buf '\\'; string_literal buf lexbuf }
  | "\\n"        { Buffer.add_char buf '\n'; string_literal buf lexbuf }
  | "\\t"        { Buffer.add_char buf '\t'; string_literal buf lexbuf }
  | '\n'         { error "unterminated string" }
  | eof          { error "unterminated string" }
  | _ as c       { Buffer.add_char buf c;    string_literal buf lexbuf }
