open ParserComb

(* type   ::= atom ('|' atom)*
   atom   ::= IDENT | object
   object ::= '{' (field (sep field)* sep?)? '}'
   field  ::= IDENT ':' type
   sep    ::= ';' | ','

   Each rule is written [let rec name st = ... st] rather than [let rec name =
   ...]. The trailing st keeps it a syntactic function, which OCaml's value
   restriction requires inside a recursive group. *)

let rec ty st = chainl1 atomic_type union_op st

(* Yields the function that builds the node, so chainl1 can fold left:
   a | b | c parses as ((a | b) | c). *)
and union_op st = 
   (token Token.BAR *> 
   return (fun a b -> Ast.TypeUnion (a, b))) 
   st

and atomic_type st =
  (choice
     [
       (ident >>| fun n -> Ast.TypeName n);
       (* singleton types, which discriminated unions are built from *)
       (str_lit >>| fun s -> Ast.TypeLit (Ast.LitStr s));
       (number >>| fun n -> Ast.TypeLit (Ast.LitNum n));
       object_type;
     ]
  <?> "a type")
    st

and object_type st =
  (between (token Token.LBRACE) (token Token.RBRACE)
     (sep_by_trailing separator field)
  >>| fun fields -> Ast.TypeObject { fields })
    st

(* Type literals accept both separators, unlike value literals. *)
and separator st = (token Token.SEMICOLON <|> token Token.COMMA) st

and field st =
  (let* name = ident in
   let* _ = token Token.COLON in
   let* t = ty in
   return ({ name; ty = t } : Ast.field))
   st
