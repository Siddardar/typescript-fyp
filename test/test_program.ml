open Ts_hoare_logic

let parse_program src = Parser.of_string src

let failures = ref 0
let total = ref 0

let check src expected =
  incr total;
  match parse_program src with
  | ast when Ast.show_program ast = expected -> ()
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected: %s\n      actual:   %s\n" src expected
        (Ast.show_program ast)
  | exception Parser.Syntax_error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match parse_program src with
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S should not parse, got %s\n" src (Ast.show_program ast)
  | exception Parser.Syntax_error _ -> ()

(* --- type aliases -------------------------------------------------------- *)

let () =
  check "type Box = string" "type Box = string;";
  check "type Box = string | number" "type Box = string | number;";
  (* the alias from _refs/ts/testing/test.ts *)
  check "type Box = { v: string | number }" "type Box = { v: string | number };";
  check "type Empty = {}" "type Empty = {};";
  check "type Nested = { a: { b: string } }" "type Nested = { a: { b: string } };"

(* --- the optional semicolon ----------------------------------------------

   A trailing ';' is accepted but not required. Ast.show_program always emits
   one, so the expected strings record that normalisation. *)

let () =
  check "type Box = string;" "type Box = string;";
  check "type Box = string" "type Box = string;";
  check "type A = string; type B = number" "type A = string;\ntype B = number;";
  check "type A = string type B = number" "type A = string;\ntype B = number;"

(* --- several declarations ------------------------------------------------ *)

let () =
  check "" "";
  check "type A = string\ntype B = number" "type A = string;\ntype B = number;";
  check "type A = string\ntype B = number\ntype C = A | B"
    "type A = string;\ntype B = number;\ntype C = A | B;";
  (* whitespace and comments between declarations *)
  check "type A = string\n\n// a comment\ntype B = number"
    "type A = string;\ntype B = number;";
  check "/* leading */ type A = string" "type A = string;"

(* --- rejections ---------------------------------------------------------- *)

let () =
  (* missing name *)
  check_rejects "type = string";
  (* missing '=' *)
  check_rejects "type Box string";
  (* missing right-hand side *)
  check_rejects "type Box =";
  check_rejects "type Box";
  (* missing 'type' *)
  check_rejects "Box = string";
  check_rejects "{ v: string }";
  (* a keyword cannot be an alias name *)
  check_rejects "type type = string";
  check_rejects "type if = string";
  (* trailing junk *)
  check_rejects "type Box = string type";
  check_rejects "type A = string }";
  (* a lone semicolon is not a declaration *)
  check_rejects ";"

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
