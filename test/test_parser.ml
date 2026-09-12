open Ts_hoare_logic

(* Types are not a top-level form, so reach the type entry point directly. *)
let parse_type src = Parse.of_string TypeParser.ty_entry src

let failures = ref 0
let total = ref 0

let check_parse src expected =
  incr total;
  match parse_type src with
  | ast when Ast.show_type ast = expected -> ()
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected: %s\n      actual:   %s\n" src expected
        (Ast.show_type ast)
  | exception Parse.Syntax_error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match parse_type src with
  | ast ->
      incr failures;
      Printf.printf "FAIL  %S should not parse, got %s\n" src (Ast.show_type ast)
  | exception Parse.Syntax_error _ -> ()

(* --- names and unions --------------------------------------------------- *)

let () =
  check_parse "string" "string";
  check_parse "number" "number";
  check_parse "Box" "Box";
  check_parse "string | number" "string | number";
  check_parse "a | b | c" "a | b | c";
  (* whitespace and newlines are insignificant *)
  check_parse "  string   |   number  " "string | number";
  check_parse "a\n| b" "a | b"

(* --- object types ------------------------------------------------------- *)

let () =
  check_parse "{}" "{}";
  check_parse "{ v: string }" "{ v: string }";
  check_parse "{v:string}" "{ v: string }";
  check_parse "{ a: string; b: number }" "{ a: string; b: number }";
  check_parse "{ a: string; b: number; c: Box }" "{ a: string; b: number; c: Box }";
  (* a trailing separator is allowed *)
  check_parse "{ a: string; }" "{ a: string }";
  check_parse "{ a: string; b: number; }" "{ a: string; b: number }"

(* --- field separators ---------------------------------------------------

   ';' and ',' are both accepted, and may be mixed. Ast.show_type always prints ';',
   so the expected strings below record that normalisation. *)

let () =
  check_parse "{ a: string, b: number }" "{ a: string; b: number }";
  check_parse "{ a: string; b: number }" "{ a: string; b: number }";
  (* trailing separator of either kind *)
  check_parse "{ a: string, }" "{ a: string }";
  check_parse "{ a: string; }" "{ a: string }";
  (* mixing is allowed, in both orders *)
  check_parse "{ a: string, b: number; c: Box }" "{ a: string; b: number; c: Box }";
  check_parse "{ a: string; b: number, c: Box }" "{ a: string; b: number; c: Box }";
  check_parse "{ a: string; b: number, }" "{ a: string; b: number }"

let () =
  (* a separator needs a field on each side *)
  check_rejects "{ , }";
  check_rejects "{ , a: string }";
  check_rejects "{ a: string,, b: number }";
  check_rejects "{ a: string;; b: number }";
  check_rejects "{ a: string,; b: number }"

(* --- the two layers compose -------------------------------------------- *)

let () =
  (* a field's type is a full type, so unions nest inside fields *)
  check_parse "{ v: string | number }" "{ v: string | number }";
  (* an object type is an atom, so objects nest inside unions *)
  check_parse "{a: string} | {b: number}" "{ a: string } | { b: number }";
  check_parse "string | {a: number}" "string | { a: number }";
  (* objects nest inside objects *)
  check_parse "{ outer: { inner: string } }" "{ outer: { inner: string } }";
  check_parse "{ a: { b: { c: string } } }" "{ a: { b: { c: string } } }";
  (* the Box type from refs/ts/testing/test.ts *)
  check_parse "{ v: string | number }" "{ v: string | number }"

(* --- rejections --------------------------------------------------------- *)

let () =
  (* incomplete unions *)
  check_rejects "|";
  check_rejects "a |";
  check_rejects "| a";
  (* trailing junk *)
  check_rejects "a b";
  check_rejects "{} {}";
  (* malformed fields *)
  check_rejects "{ v }";
  check_rejects "{ : string }";
  check_rejects "{ v: }";
  check_rejects "{ v string }";
  (* unbalanced braces *)
  check_rejects "{ v: string";
  check_rejects "}";
  check_rejects "{ a: { b: string }";
  (* missing separator between fields *)
  check_rejects "{ a: string b: number }";
  (* not supported: numeric field names *)
  check_rejects "{ 1: string }";
  (* empty input *)
  check_rejects ""

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
