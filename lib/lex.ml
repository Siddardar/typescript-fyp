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
