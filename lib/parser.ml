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