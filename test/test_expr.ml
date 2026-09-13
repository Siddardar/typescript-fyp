open Ts_hoare_logic

let failures = ref 0
let total = ref 0

(* An expression is not a top-level form, so drive the grammar directly. *)
let parse_expr src =
  ExprParser.expr_entry (ParserState.make (Lex.tokenise (Lexing.from_string src)))

let check src expected =
  incr total;
  match parse_expr src with
  | ast when Ast.show_expr ast = expected -> ()
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected: %s\n      actual:   %s\n" src expected
        (Ast.show_expr ast)
  | exception ParserState.Error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match parse_expr src with
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S should not parse, got %s\n" src (Ast.show_expr ast)
  | exception ParserState.Error _ -> ()
  | exception Lexer.Error _ -> ()

(* --- primary ------------------------------------------------------------- *)

let () =
  check "x" "x";
  check "foo_bar" "foo_bar";
  check "42" "42";
  check "3.14" "3.14";
  check "0" "0";
  check {|"hello"|} {|"hello"|};
  check {|""|} {|""|};
  (* parentheses group, but leave no node behind *)
  check "(x)" "x";
  check "((x))" "x";
  check_rejects "";
  check_rejects "(";
  check_rejects "(x";
  check_rejects "()"

(* --- postfix: member and call -------------------------------------------- *)

let () =
  check "b.v" "b.v";
  check "b.v.w" "b.v.w";
  check "f()" "f()";
  check "f(x)" "f(x)";
  check "f(x, y)" "f(x, y)";
  check "f(x, y, z)" "f(x, y, z)";
  (* chaining, left to right *)
  check "b.v.toUpperCase()" "b.v.toUpperCase()";
  check "f(x)(y)" "f(x)(y)";
  check "f().g" "f().g";
  (* nesting *)
  check "f(g(x))" "f(g(x))";
  check "f(a.b, g(c))" "f(a.b, g(c))";
  check "console.log(b.v.toUpperCase())" "console.log(b.v.toUpperCase())";
  check_rejects "b.";
  check_rejects "f(";
  check_rejects "f(x";
  check_rejects "f(x,)";
  check_rejects "b..v"

(* --- unary --------------------------------------------------------------- *)

let () =
  check "typeof x" "(typeof x)";
  (* binds looser than member access, so the whole b.v is the operand *)
  check "typeof b.v" "(typeof b.v)";
  check "typeof f(x)" "(typeof f(x))";
  (* prefix operators stack *)
  check "typeof typeof x" "(typeof (typeof x))";
  check_rejects "typeof"

(* --- equality, left-associative ------------------------------------------ *)

let () =
  check "a === b" "(a === b)";
  check "a !== b" "(a !== b)";
  check "a === b === c" "((a === b) === c)";
  check "a === b !== c" "((a === b) !== c)";
  (* parens override the grouping *)
  check "a === (b === c)" "(a === (b === c))";
  check_rejects "=== b";
  check_rejects "a ==="

(* --- assignment, right-associative --------------------------------------- *)

let () =
  check "x = 5" "(x = 5)";
  check "b.v = 42" "(b.v = 42)";
  check "x = y = 0" "(x = (y = 0))";
  check "b.v = f(x)" "(b.v = f(x))";
  (* '=' binds looser than '===' *)
  check "x = a === b" "(x = (a === b))";
  (* only an identifier or member may be assigned to *)
  check_rejects "42 = x";
  check_rejects {|"s" = x|};
  check_rejects "f(x) = 1";
  check_rejects "(a === b) = 1";
  check_rejects "x ="

(* --- object literals ------------------------------------------------------

   Unlike type literals, value literals take ',' only — {a: 1; b: 2} is not
   valid TypeScript. A trailing comma is allowed. *)

let () =
  check "{}" "{}";
  check {|{v: "hello"}|} {|{ v: "hello" }|};
  check "{a: 1, b: 2}" "{ a: 1, b: 2 }";
  check "{a: 1, b: 2, c: 3}" "{ a: 1, b: 2, c: 3 }";
  check "{a: 1,}" "{ a: 1 }";
  check "{ a : 1 }" "{ a: 1 }";
  (* a property value is a full expression *)
  check "{a: f(x)}" "{ a: f(x) }";
  check "{a: b.c}" "{ a: b.c }";
  check "{a: b === c}" "{ a: (b === c) }";
  check "{a: typeof b}" "{ a: (typeof b) }";
  (* nesting, both directions *)
  check "{a: {b: 1}}" "{ a: { b: 1 } }";
  check {|f({v: "hello"})|} {|f({ v: "hello" })|};
  check "f({})" "f({})";
  check "f({a: 1}, {b: 2})" "f({ a: 1 }, { b: 2 })";
  (* an object literal is a primary, so postfix applies to it *)
  check "{a: 1}.a" "{ a: 1 }.a";
  check_rejects "{a}";
  check_rejects "{: 1}";
  check_rejects "{a:}";
  check_rejects "{a 1}";
  check_rejects "{a: 1";
  check_rejects "{a: 1,, b: 2}";
  check_rejects "{,}";
  (* ';' is a type-literal separator, not a value-literal one *)
  check_rejects "{a: 1; b: 2}"

(* --- precedence, all levels together ------------------------------------- *)

let () =
  check {|typeof b.v === "string"|} {|((typeof b.v) === "string")|};
  check {|x = typeof b.v === "string"|} {|(x = ((typeof b.v) === "string"))|};
  check "a.b(c).d === e.f" "(a.b(c).d === e.f)";
  (* every construct at once *)
  check {|f({v: typeof b.v === "string"})|}
    {|f({ v: ((typeof b.v) === "string") })|};
  (* the two expressions from _refs/ts/testing/test.ts *)
  check "b.v = 42" "(b.v = 42)";
  check {|typeof b.v === "string"|} {|((typeof b.v) === "string")|};
  check "console.log(b.v.toUpperCase())" "console.log(b.v.toUpperCase())";
  check {|f({v: "hello"})|} {|f({ v: "hello" })|}

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
