open ParserComb

exception Syntax_error of string

(* program ::= statement* *)

(* stops at the first token that cannot start a statement, so the
   failure surfaces as the end-of-input check. *)
let program =
  many StmtParser.statement <* (eof <?> "a statement or end of input")

(* --- entry points -------------------------------------------------------- *)

let parse_lexbuf lexbuf =
  (* lexing happens first, catch lexer error before run *)
  let tokens =
    try Lex.tokenise lexbuf with
    | Lexer.Error msg ->
        let p = Lexing.lexeme_start_p lexbuf in
        raise
          (Syntax_error
             (Printf.sprintf "line %d, col %d: %s" p.pos_lnum
                (p.pos_cnum - p.pos_bol + 1) msg))
  in
  match run program tokens with
  | Ok ast -> ast
  | Error msg -> raise (Syntax_error msg)

let of_string src = parse_lexbuf (Lexing.from_string src)

let of_file file_path =
  let in_chan = open_in_bin file_path in

  Fun.protect
    ~finally:(fun () -> close_in in_chan)
    (fun () ->
      let lexbuf = Lexing.from_channel in_chan in
      Lexing.set_filename lexbuf file_path;

      parse_lexbuf lexbuf)
