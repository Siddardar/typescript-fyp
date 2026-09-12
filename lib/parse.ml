exception Syntax_error of string

let tokenise lexbuf =
  let acc = ref [] in
  let rec loop () =
    let token = Lexer.read lexbuf in
    let pos = Lexing.lexeme_start_p lexbuf in

    let located_token : Token.located =
      { token; line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 }
    in

    acc := located_token :: !acc;

    if token <> Token.EOF then loop ()
  in

  loop ();

  Array.of_list (List.rev !acc)

let parse_with entry lexbuf =
  try entry (ParserState.make (tokenise lexbuf)) with
  | ParserState.Error msg -> raise (Syntax_error msg)
  | Lexer.Error msg ->
      let p = Lexing.lexeme_start_p lexbuf in
      raise
        (Syntax_error
           (Printf.sprintf "line %d, col %d: %s" p.pos_lnum
              (p.pos_cnum - p.pos_bol + 1) msg))

(* for testing *)
let of_string entry str = parse_with entry (Lexing.from_string str)

let of_file entry file_path =
  let in_chan = open_in_bin file_path in

  Fun.protect
    ~finally:(fun () -> close_in in_chan)
    (fun () ->
      let lexbuf = Lexing.from_channel in_chan in
      Lexing.set_filename lexbuf file_path;

      parse_with entry lexbuf)
