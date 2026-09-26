open Ts_hoare_logic

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    incr failures;
    Printf.printf "FAIL  %s\n" name)

(* Elaborate a source program, then look up one alias. *)
let elab src name =
  let env = Elab.program (Parser.of_string src) in
  List.assoc name env

let check_elab src name expected =
  incr total;
  match elab src name with
  | actual when Ty.show actual = expected -> ()
  | actual ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected: %s\n      actual:   %s\n" src expected
        (Ty.show actual)
  | exception Elab.Error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match Elab.program (Parser.of_string src) with
  | _ ->
      incr failures;
      Printf.printf "FAIL  %S should not elaborate\n" src
  | exception Elab.Error _ -> ()

(* --- builtins -------------------------------------------------------------- *)

let () =
  check_elab "type T = string" "T" "string";
  check_elab "type T = number" "T" "number";
  check_elab "type T = boolean" "T" "boolean";
  check_elab "type T = unknown" "T" "unknown";
  check_elab "type T = never" "T" "never";
  check_elab "type T = true" "T" "true";
  check_elab "type T = false" "T" "false"

(* --- singleton types ------------------------------------------------------- *)

let () =
  check_elab {|type T = "circle"|} "T" {|"circle"|};
  check_elab "type T = 42" "T" "42";
  check_elab {|type T = "a" | "b"|} "T" {|"a" | "b"|};
  (* a singleton sits inside its base type *)
  check "a literal is below its base"
    (Subty.subty (elab {|type T = "a"|} "T") Ty.string_);
  check "distinct literals are disjoint"
    (Empty.is_empty (Ty.and_ (elab {|type T = "a"|} "T") (elab {|type T = "b"|} "T")))

(* --- unions ---------------------------------------------------------------- *)

let () =
  check_elab "type T = string | number" "T" "string | number";
  check_elab "type T = string | number | boolean" "T" "string | number | boolean";
  (* the smart constructors normalise during elaboration *)
  check_elab "type T = string | string" "T" "string";
  check_elab "type T = string | never" "T" "string";
  check_elab "type T = string | unknown" "T" "unknown"

(* --- object types become anonymous open rows -------------------------------

   The anonymous token makes them structural; open means "at least these
   fields", which is where width subtyping comes from. *)

let () =
  check_elab "type T = {}" "T" {|{ %tag: "" }|};
  check_elab "type T = { x: string }" "T" {|{ %tag: "", x: string }|};
  check_elab "type T = { x: string; y: number }" "T"
    {|{ %tag: "", x: string, y: number }|};
  check_elab "type T = { v: string | number }" "T" {|{ %tag: "", v: string | number }|};
  check_elab "type T = { a: { b: string } }" "T"
    {|{ %tag: "", a: { %tag: "", b: string } }|};
  check_rejects "type T = { x: string; x: number }"

(* --- aliases --------------------------------------------------------------- *)

let () =
  check_elab "type A = string\ntype B = A" "B" "string";
  check_elab "type A = string\ntype B = { x: A }" "B" {|{ %tag: "", x: string }|};
  check_elab "type A = string\ntype B = number\ntype C = A | B" "C" "string | number";
  (* forward references work: aliases are collected before any is elaborated *)
  check_elab "type B = A\ntype A = string" "B" "string";
  check_elab "type C = { x: A }\ntype A = number" "C" {|{ %tag: "", x: number }|};
  (* but a cycle is rejected: recursive types need the predicate layer *)
  check_rejects "type A = A";
  check_rejects "type A = B\ntype B = A";
  check_rejects "type A = { x: A }";
  (* and so are unknown names and duplicate declarations *)
  check_rejects "type A = Nope";
  check_rejects "type A = string\ntype A = number"

(* --- any is rejected --------------------------------------------------------

   any is assignable in both directions, so it denotes no set of values and has
   no reading under semantic subtyping. Paper A appendix B.2 handles it with
   gradual typing casts, which is future work. *)

let () = check_rejects "type T = any"

(* --- the whole pipeline, on a discriminated union --------------------------

   Source text to a decided subtyping question, through lexer, parser,
   elaboration, and the emptiness test. *)

let () =
  let src =
    {|type Circle = { kind: "circle"; r: number }
      type Square = { kind: "square"; w: number }
      type Shape = Circle | Square|}
  in
  let env = Elab.program (Parser.of_string src) in
  let circle = List.assoc "Circle" env in
  let square = List.assoc "Square" env in
  let shape = List.assoc "Shape" env in
  check "an arm is below the union" (Subty.subty circle shape);
  check "the union is not below an arm" (not (Subty.subty shape circle));
  check "the arms are disjoint" (Empty.is_empty (Ty.and_ circle square));
  check "the arms are exhaustive"
    (Subty.exhaustive ~scrutinee:shape ~arms:[ circle; square ]);
  check "one arm is not exhaustive"
    (not (Subty.exhaustive ~scrutinee:shape ~arms:[ circle ]));
  check "narrowing by the discriminant"
    (Subty.equiv
       (Subty.refine shape ~by:(Ty.record [ ("kind", Ty.str "circle") ]))
       circle)

(* --- the Box type from _refs/ts/testing/test.ts --------------------------- *)

let () =
  let env = Elab.program (Parser.of_string "type Box = { v: string | number }") in
  let box = List.assoc "Box" env in
  let box_str = Ty.record [ ("v", Ty.string_) ] in
  check "the narrowed box is below Box" (Subty.subty box_str box);
  check "Box is not below the narrowed box" (not (Subty.subty box box_str))

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
