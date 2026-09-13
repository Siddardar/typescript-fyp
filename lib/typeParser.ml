open ParserState

let rec ty state = 
  let rec loop lhs = 
    match peek_token state with
    | Token.BAR ->
      advance_pos state;
      
      let rhs = atomic_type state in
      loop (Ast.TypeUnion (lhs, rhs))
  
    | _ -> lhs
  in

  loop (atomic_type state)

  and atomic_type state = 
    match peek_token state with
    | Token.IDENT n -> 
        advance_pos state;
        Ast.TypeName n
    
    | Token.LBRACE -> 
      object_type state
    
    | _ -> failure_msg state "a type name or '{'"

  and object_type state = 
    expect_token state Token.LBRACE "'{'";

    let rec loop fields = 
      match peek_token state with
      | Token.RBRACE -> 
        advance_pos state;
        Ast.TypeObject { fields = List.rev fields }
      
      | Token.IDENT _ -> 
        let field = object_field state in
        begin
          match peek_token state with
          | Token.SEMICOLON | Token.COMMA -> 
            advance_pos state;
            loop(field :: fields)
          
          | Token.RBRACE -> loop (field :: fields)
          
          | _ -> failure_msg state "';', ',' or '}'"
        end
      
      | _ -> failure_msg state "a field name or '}'"
    in

    loop []

  and object_field state = 
    match peek_token state with 
    | Token.IDENT name -> 
      advance_pos state;
      expect_token state Token.COLON "':'";

      let field_type = ty state in
      { Ast.name; ty = field_type }

    | _ -> failure_msg state "a field name"

let ty_entry state = 
  let t = ty state in
  
  expect_token state Token.EOF "end of input";
  t
