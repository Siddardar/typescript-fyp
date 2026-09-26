let tokenise lexbuf = 
  let rec loop acc = 
    let token = Lexer.read lexbuf in 
    let pos = Lexing.lexeme_start_p lexbuf in

    let located_token : Token.located = {
      token;
      line = pos.pos_lnum;
      col = pos.pos_cnum - pos.pos_bol + 1 (* 1 based for readability *)
    } in
    
    let acc = located_token :: acc in

    if token = Token.EOF then 
      Array.of_list ( List.rev acc )
    else
      loop acc
  in

  loop []