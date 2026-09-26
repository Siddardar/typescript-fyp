open Ts_hoare_logic

let failures = ref 0
let total = ref 0
let parse src = Parser.of_string src

let check src expected =
  incr total;
  match parse src with
  | ast when Ast.show_program ast = expected -> ()
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected:\n%s\n      actual:\n%s\n" src expected
        (Ast.show_program ast)
  | exception Parser.Syntax_error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match parse src with
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S should not parse, got %s\n" src (Ast.show_program ast)
  | exception Parser.Syntax_error _ -> ()

(* --- expression statements ----------------------------------------------- *)

let () =
  check "f(x);" "f(x);";
  check "f(x)" "f(x);";
  check "b.v = 42;" "(b.v = 42);";
  check {|f({v: "hello"});|} {|f({ v: "hello" });|};
  check "f(x); g(y);" "f(x);\ng(y);";
  (* A divergence from tsc: ';' is fully optional here, so two statements on
     one line are accepted. Matching tsc needs automatic semicolon insertion,
     which needs the lexer to treat newlines as significant. *)
  check "f(x) g(y)" "f(x);\ng(y);"

(* --- blocks ---------------------------------------------------------------

   A '{' at statement position opens a block, not an object literal. That is
   how TypeScript reads it too, so {a: 1}.a is valid as an expression but not
   as a statement. *)

let () =
  check "{}" "{}";
  check "{ f(x); }" "{\n  f(x);\n}";
  check "{ f(x); g(y); }" "{\n  f(x);\n  g(y);\n}";
  check "{ { f(x); } }" "{\n  {\n    f(x);\n  }\n}";
  check_rejects "{a: 1}.a;";
  check_rejects "{ f(x);"

(* --- variable declarations ------------------------------------------------ *)

let () =
  check "let x = 1;" "let x = 1;";
  check "const x = 1;" "const x = 1;";
  check "let x: number = 1;" "let x: number = 1;";
  check "let x: string | number = 1;" "let x: string | number = 1;";
  check "let b: Box = f(x);" "let b: Box = f(x);";
  check "let x = 1" "let x = 1;";
  check_rejects "let x;";
  check_rejects "let = 1;";
  check_rejects "let x: = 1;";
  check_rejects "let x = ;"

(* --- return --------------------------------------------------------------- *)

let () =
  check "return;" "return;";
  check "return x;" "return x;";
  check "return f(x);" "return f(x);";
  check "return" "return;";
  check "return a === b;" "return (a === b);"

(* --- if ------------------------------------------------------------------- *)

let () =
  check "if (a) f();" "if (a) \n  f();";
  check "if (a) { f(); }" "if (a) {\n  f();\n}";
  check "if (a) { f(); } else { g(); }" "if (a) {\n  f();\n} else {\n  g();\n}";
  check {|if (typeof b.v === "string") { f(); }|}
    "if (((typeof b.v) === \"string\")) {\n  f();\n}";
  (* a dangling else binds to the nearest if *)
  check "if (a) if (b) f(); else g();"
    "if (a) \n  if (b) \n    f(); else \n    g();";
  check_rejects "if a f();";
  check_rejects "if (a)";
  check_rejects "else f();"

(* --- functions ------------------------------------------------------------ *)

let () =
  check "function f() {}" "function f() {}";
  check "function f(b: Box) {}" "function f(b: Box) {}";
  check "function f(a: string, b: number) {}" "function f(a: string, b: number) {}";
  check "function f(): number {}" "function f(): number {}";
  check "function f(b: Box): string | number {}" "function f(b: Box): string | number {}";
  check "function f() { return 1; }" "function f() {\n  return 1;\n}";
  check "function mutate(b: Box) { b.v = 42; }"
    "function mutate(b: Box) {\n  (b.v = 42);\n}";
  check_rejects "function () {}";
  check_rejects "function f {}";
  check_rejects "function f(b) {}";
  check_rejects "function f()"

(* --- mixed top level ------------------------------------------------------ *)

let () =
  check "type A = string\nlet x: A = \"a\";" "type A = string;\nlet x: A = \"a\";";
  check "type A = string function f() {}" "type A = string;\nfunction f() {}"

(* --- the whole of _refs/ts/testing/test.ts -------------------------------- *)

let () =
  check
    {|type Box = { v: string | number }

function mutate(b: Box) { b.v = 42; }

function f(b: Box) {
    if (typeof b.v === "string") {
        mutate(b);
        console.log(b.v.toUpperCase());
    }
}

f({v: "hello"});|}
    {|type Box = { v: string | number };
function mutate(b: Box) {
  (b.v = 42);
}
function f(b: Box) {
  if (((typeof b.v) === "string")) {
    mutate(b);
    console.log(b.v.toUpperCase());
  }
}
f({ v: "hello" });|}

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
