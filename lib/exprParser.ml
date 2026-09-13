open ParserState

let rec expr state = assignment state
  and assignment state =
    let lhs = equality state in

    match peek_token state with 
    | Token.EQUALS -> 
      (match lhs with 
      | Ast.Ident _ | Ast.Member _ -> ()
      | _ -> failure_msg state "a var or property of lhs of '='");

      advance_pos state;
      let rhs = assignment state in

      Ast.Assign (lhs, rhs)
    
    | _ -> lhs
    
  and equality state = 
    let rec loop lhs = 
      let op = 
        match peek_token state with 
        | Token.EQ_CHECK -> Some Ast.StrictEq
        | Token.NEQ_CHECK -> Some Ast.StrictNeq
        | _ -> None
      in

      match op with
      | None -> lhs
      | Some op -> 
        advance_pos state;
        let rhs = unary state in
        loop (Ast.Binary (op, lhs, rhs))
    in
    
    loop(unary state)
  
  and unary state = 
    match peek_token state with 
    | Token.KW_TYPEOF -> 
      advance_pos state;
      Ast.Unary (Ast.TypeOf, unary state)
    | _ -> postfix state
  
  and postfix state = 
    let rec loop exp =
      match peek_token state with
      | Token.DOT ->
          advance_pos state;
          let name = expect_ident state in
          
          loop (Ast.Member (exp, name))
      
      | Token.LPAREN ->
          advance_pos state;
          let a = args state in
          expect_token state Token.RPAREN "')'";
          
          loop (Ast.Call (exp, a))
      
      | _ -> exp
    in
    loop (primary state)
  
  and primary state =
    match peek_token state with 
    | Token.IDENT name ->
      advance_pos state;
      Ast.Ident name
    
    | Token.NUMBER num -> 
      advance_pos state;
      Ast.Number num

    | Token.STRING str -> 
      advance_pos state;
      Ast.String str

    | Token.LPAREN -> 
      advance_pos state;
      let inner = expr state in
      expect_token state Token.RPAREN "')'";
      inner

    | Token.LBRACE ->
      advance_pos state;
      object_literal state
    
    | _ -> failure_msg state "an expression"
  
  and object_literal state =
    let rec loop props =
      match peek_token state with
      | Token.RBRACE ->
          advance_pos state;
          Ast.ObjectLit (List.rev props)

      | Token.IDENT _ ->
          let name = expect_ident state in
          expect_token state Token.COLON "':'";
          let value = expr state in
          let p = { Ast.name; value } in

          begin
            match peek_token state with
            | Token.COMMA ->
                advance_pos state;
                loop (p :: props)
            | Token.RBRACE -> loop (p :: props)
            | _ -> failure_msg state "',' or '}'"
          end

      | _ -> failure_msg state "a property name or '}'"
    in

    loop []

  and args state = 
    match peek_token state with 
    | Token.RPAREN -> []
    | _ -> 
      let rec loop acc = 
        let e = expr state in
        match peek_token state with 
        | Token.COMMA -> 
          advance_pos state;
          loop (e :: acc)
        | _ -> List.rev (e :: acc)
      in

      loop []

let expr_entry state = 
  let e = expr state in

  expect_token state Token.EOF "end of input";
  e