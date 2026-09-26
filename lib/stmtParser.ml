open ParserComb

(* statement ::= 'type' IDENT '=' type ';'?
               | 'function' IDENT '(' params ')' (':' type)? block
               | 'if' '(' expr ')' statement ('else' statement)?
               | ('let' | 'const') IDENT (':' type)? '=' expr ';'?
               | 'return' expr? ';'?
               | block
               | expr ';'?
   block     ::= '{' statement* '}'
   params    ::= e | param (',' param)*
   param     ::= IDENT ':' type

   Branch order matters in two places. [block] must be tried before
   [expr_stmt], so a leading '{' is a block rather than an object literal —
   which is how TypeScript reads it too. And [expr_stmt] must come last,
   because an expression can start with almost any token. *)

(* TODO: Implement TypeScript automatic semicolon insertion. Newlines are
   currently discarded by the lexer, so making ';' unconditionally optional
   accepts invalid same-line statements and misparses cases such as [return\n x]. *)

let semi = opt (token Token.SEMICOLON)

let rec statement st =
  (choice
     [ 
        type_alias;
        function_decl;
        if_stmt;
        var_decl;
        return_stmt;
        block_stmt;
        expr_stmt
      ]
  <?> "a statement")
    st

and type_alias st =
  (let* _ = token Token.KW_TYPE in
   let* name = ident in
   let* _ = token Token.EQUALS in
   let* ty = TypeParser.ty in
   let* _ = semi in
   return (Ast.TypeAlias { name; ty }))
    st

and function_decl st =
  (let* _ = token Token.KW_FUNCTION in
   let* name = ident in
   let* params =
     between (token Token.LPAREN) (token Token.RPAREN) (sep_by (token Token.COMMA) param)
   in
   let* ret_type = opt (token Token.COLON *> TypeParser.ty) in
   let* body = block in
   return (Ast.FunctionDecl { name; params; ret_type; body }))
    st

and param st =
  (let* name = ident in
   let* _ = token Token.COLON in
   let* ty = TypeParser.ty in
   return ({ name; ty } : Ast.param))
    st

(* The optional else is parsed greedily by the innermost if, which binds a
   dangling else to the nearest one — the usual reading. *)
and if_stmt st =
  (let* _ = token Token.KW_IF in
   let* cond = between (token Token.LPAREN) (token Token.RPAREN) ExprParser.expr in
   let* then_ = statement in
   let* else_ = opt (token Token.KW_ELSE *> statement) in
   return (Ast.If { cond; then_; else_ }))
    st

and var_decl st =
  (let* kind =
     (token Token.KW_LET *> return Ast.Let) <|> (token Token.KW_CONST *> return Ast.Const)
   in
   let* name = ident in
   let* ty = opt (token Token.COLON *> TypeParser.ty) in
   let* _ = token Token.EQUALS in
   let* value = ExprParser.expr in
   let* _ = semi in
   return (Ast.VarDecl { kind; name; ty; value }))
    st

and return_stmt st =
  (let* _ = token Token.KW_RETURN in
   let* e = opt ExprParser.expr in
   let* _ = semi in
   return (Ast.Return e))
    st

and block st =
  between (token Token.LBRACE) (token Token.RBRACE) (many statement) st

and block_stmt st = (block >>| fun body -> Ast.Block body) st

and expr_stmt st =
  (let* e = ExprParser.expr in
   let* _ = semi in
   return (Ast.ExprStmt e))
    st
