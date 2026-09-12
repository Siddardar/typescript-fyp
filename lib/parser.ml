exception Syntax_error of string
open ParserState

let declaration state = 
  expect_token state Token.KW_TYPE "'type'";

  let name = expect_ident state in
  expect_token state Token.EQUALS "'='";

  let ty = TypeParser.ty state in
  if peek_token state = Token.SEMICOLON then advance_pos state;

  Ast.TypeAlias { name; ty }

let program state = 
  let rec loop declarations = 
    match peek_token state with 
    | Token.EOF -> List.rev declarations
    | _ -> 
      let d = declaration state in
      loop (d :: declarations)
  in

  loop([])

let program_entry state = 
  let declarations = program state in
  expect_token state Token.EOF "end of input";
  declarations

let parse_lexbuf lexbuf =
  try program_entry (ParserState.make (Lex.tokenise lexbuf)) with
  | ParserState.Error msg -> raise (Syntax_error msg)
  | Lexer.Error msg ->
      let p = Lexing.lexeme_start_p lexbuf in
      raise
        (Syntax_error
           (Printf.sprintf "line %d, col %d: %s" p.pos_lnum
              (p.pos_cnum - p.pos_bol + 1) msg))

let of_string src = parse_lexbuf (Lexing.from_string src)

let of_file file_path =
  let in_chan = open_in_bin file_path in

  Fun.protect
    ~finally:(fun () -> close_in in_chan)
    (fun () ->
      let lexbuf = Lexing.from_channel in_chan in
      Lexing.set_filename lexbuf file_path;

      parse_lexbuf lexbuf)
