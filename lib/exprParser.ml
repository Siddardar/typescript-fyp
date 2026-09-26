open ParserComb

(* expr       ::= assignment
   assignment ::= equality ('=' assignment)?            right-assoc
   equality   ::= unary (('===' | '!==') unary)*        left-assoc
   unary      ::= 'typeof' unary | postfix              prefix ops stack
   postfix    ::= primary ('.' IDENT | '(' args ')')*   left-assoc
   primary    ::= IDENT | NUMBER | STRING | '(' expr ')' | object
   object     ::= '{' (prop (',' prop)* ','?)? '}'
   prop       ::= IDENT ':' expr
   args       ::= e | expr (',' expr)*                  no trailing comma

   The nesting is the precedence: each level parses its operands with the next
   tighter one. *)

let rec expr st = assignment st

(* Only an identifier or a member access may be assigned to. The check runs
   after '=' is consumed, so its failure is committed and alt will not fall
   back to treating the left side as a complete expression. *)
and assignment st =
  (let* lhs = equality in
   alt
     (let* _ = token Token.EQUALS in
      let* _ =
        match lhs with
        | Ast.Ident _ | Ast.Member _ -> return ()
        | _ -> fail "a variable or property on the left of '='"
      in
      let* rhs = assignment in
      return (Ast.Assign (lhs, rhs)))
     (return lhs))
    st

and equality st = chainl1 unary equality_op st

and equality_op st =
  ((token Token.EQ_CHECK *> return (fun a b -> Ast.Binary (Ast.StrictEq, a, b)))
  <|> 
  (token Token.NEQ_CHECK *> return (fun a b -> Ast.Binary (Ast.StrictNeq, a, b))))
    st

(* Recurses into itself, not postfix, so typeof typeof x parses. *)
and unary st =
  ((token Token.KW_TYPEOF *> unary >>| fun e -> Ast.Unary (Ast.TypeOf, e))
  <|> postfix)
    st

(* Each suffix yields a function wrapping what has been built so far, so
   b.v.toUpperCase() folds into Call (Member (Member (b, v), toUpperCase), []). *)
and postfix st =
  (let* first = primary in
   let* suffixes = many (member_suffix <|> call_suffix) in
   return (List.fold_left (fun acc f -> f acc) first suffixes))
    st

and member_suffix st =
  (token Token.DOT *> ident >>| fun name e -> Ast.Member (e, name)) st

and call_suffix st =
  (between (token Token.LPAREN) (token Token.RPAREN) args >>| fun a e -> Ast.Call (e, a))
    st

(* Parentheses group but leave no node behind. *)
and primary st =
  (choice
     [
       (ident >>| fun n -> Ast.Ident n);
       (number >>| fun n -> Ast.Number n);
       (str_lit >>| fun s -> Ast.String s);
       between (token Token.LPAREN) (token Token.RPAREN) expr;
       object_literal;
     ]
  <?> "an expression")
    st

(* Value literals take ',' only, unlike type literals. *)
and object_literal st =
  (between (token Token.LBRACE) (token Token.RBRACE)
     (sep_by_trailing (token Token.COMMA) prop)
  >>| fun props -> Ast.ObjectLit props)
    st

and prop st =
  (let* name = ident in
   let* _ = token Token.COLON in
   let* value = expr in
   return { Ast.name; value })
    st

(* No trailing comma: f(x,) is rejected. *)
and args st = sep_by (token Token.COMMA) expr st
