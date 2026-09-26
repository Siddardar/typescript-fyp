open Ts_hoare_logic
open Row

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    incr failures;
    Printf.printf "FAIL  %s\n" name)

let check_show name row expected =
  incr total;
  let actual = show Fun.id row in
  if actual <> expected then (
    incr failures;
    Printf.printf "FAIL  %s\n      expected: %s\n      actual:   %s\n" name expected actual)

(* --- one data form --------------------------------------------------------

   The four surface vocabularies differ only in the token and the label kind.
   Compare Paper B definition 3.1, page 7. *)

let () =
  check_show "anonymous record" (record [ ("x", "A"); ("y", "B") ])
    {|{ %tag: "", x: A, y: B }|};
  check_show "tuple" (tuple [ "A"; "B" ]) {|{ %tag: "", 0: A, 1: B }_c|};
  check_show "unit" unit_row {|{ %tag: "" }_c|};
  check_show "positional constructor" (constr "Cons" [ "A"; "B" ])
    "{ %tag: tok(Cons), 0: A, 1: B }_c";
  check_show "record constructor" (constr_record "Loc" [ ("x", "A"); ("y", "B") ])
    "{ %tag: tok(Loc), x: A, y: B }";
  check_show "named-positional constructor"
    (constr_named "Point" [ ("x", "A"); ("y", "B") ])
    "{ %tag: tok(Point), x@0: A, y@1: B }_c";
  (* a tuple and an anonymous record share the anonymous token and differ only
     in label kind *)
  check "tuple and record share a tag" ((tuple [ "A" ]).tag = (record [ ("x", "A") ]).tag)

(* --- answering ------------------------------------------------------------

   A composite answers both its name and its position, so p.1 and p.x reach
   the same field. That single label is the paper's unification. *)

let () =
  check "name answers name" (answers (Name "x") (Name "x"));
  check "name refuses other name" (not (answers (Name "x") (Name "y")));
  check "name refuses position" (not (answers (Name "x") (Pos 1)));
  check "position answers position" (answers (Pos 1) (Pos 1));
  check "position refuses other position" (not (answers (Pos 1) (Pos 2)));
  check "position refuses name" (not (answers (Pos 1) (Name "x")));
  check "composite answers its name" (answers (Composite ("x", 1)) (Name "x"));
  check "composite answers its position" (answers (Composite ("x", 1)) (Pos 1));
  check "composite answers itself" (answers (Composite ("x", 1)) (Composite ("x", 1)));
  check "composite refuses a wrong name" (not (answers (Composite ("x", 1)) (Name "y")));
  check "composite refuses a wrong position" (not (answers (Composite ("x", 1)) (Pos 2)));
  (* a bare name does not answer a composite demand: that needs both halves *)
  check "name refuses composite" (not (answers (Name "x") (Composite ("x", 1))))

(* --- lookup --------------------------------------------------------------- *)

let () =
  let p = constr_named "Point" [ ("x", "A"); ("y", "B") ] in
  check "p.x" (lookup (Name "x") p = Some "A");
  check "p.y" (lookup (Name "y") p = Some "B");
  check "p.0 reaches the same field as p.x" (lookup (Pos 0) p = lookup (Name "x") p);
  check "p.1 reaches the same field as p.y" (lookup (Pos 1) p = lookup (Name "y") p);
  check "p.z is absent" (lookup (Name "z") p = None);
  check "p.2 is absent" (lookup (Pos 2) p = None);
  (* a plain record has no positions, so it is read by name only *)
  let r = record [ ("x", "A") ] in
  check "record by name" (lookup (Name "x") r = Some "A");
  check "record has no position 0" (lookup (Pos 0) r = None);
  (* a plain tuple has no names *)
  let t = tuple [ "A"; "B" ] in
  check "tuple by position" (lookup (Pos 1) t = Some "B");
  check "tuple has no name x" (lookup (Name "x") t = None);
  check "mem agrees with lookup" (mem (Name "x") p && not (mem (Name "z") p))

(* --- well-keyedness -------------------------------------------------------

   No two fields may answer the same demand. Distinct names and distinct
   positions is the decidable form of that condition. *)

let () =
  check "record is well keyed" (well_keyed (record [ ("x", "A"); ("y", "B") ]));
  check "tuple is well keyed" (well_keyed (tuple [ "A"; "B"; "C" ]));
  check "named-positional is well keyed"
    (well_keyed (constr_named "P" [ ("x", "A"); ("y", "B") ]));
  check "duplicate names are rejected"
    (not (well_keyed (make ~tag:Anon ~kind:Open ~fields:[ (Name "x", "A"); (Name "x", "B") ])));
  check "duplicate positions are rejected"
    (not (well_keyed (make ~tag:Anon ~kind:Closed ~fields:[ (Pos 1, "A"); (Pos 1, "B") ])));
  (* a composite collides with a bare label that shares either half *)
  check "composite colliding on a name is rejected"
    (not
       (well_keyed
          (make ~tag:Anon ~kind:Open ~fields:[ (Composite ("x", 1), "A"); (Name "x", "B") ])));
  check "composite colliding on a position is rejected"
    (not
       (well_keyed
          (make ~tag:Anon ~kind:Open ~fields:[ (Composite ("x", 1), "A"); (Pos 1, "B") ])));
  (* a composite beside an unrelated bare label is fine *)
  check "composite beside an unrelated name is well keyed"
    (well_keyed
       (make ~tag:Anon ~kind:Open ~fields:[ (Composite ("x", 1), "A"); (Name "y", "B") ]));
  check "the empty row is well keyed" (well_keyed unit_row)

(* --- tokens ---------------------------------------------------------------

   Distinct tokens are disjoint. That single fact is where nominal typing
   comes from, with no nominal typing rule. *)

let () =
  check "distinct constructors have distinct tokens"
    ((constr "Cons" [ "A" ]).tag <> (constr "Nil" [ "A" ]).tag);
  check "the same constructor shares a token"
    ((constr "Cons" [ "A" ]).tag = (constr "Cons" [ "B" ]).tag);
  check "a constructor is not anonymous" ((constr "C" []).tag <> Anon);
  (* same shape, different constructor: unrelated *)
  check "same shape, different token"
    ((constr "Dog" [ "A" ]).fields = (constr "Cat" [ "A" ]).fields
    && (constr "Dog" [ "A" ]).tag <> (constr "Cat" [ "A" ]).tag)

(* --- width ---------------------------------------------------------------- *)

let () =
  check "a record is open" ((record [ ("x", "A") ]).kind = Open);
  check "a tuple is closed" ((tuple [ "A" ]).kind = Closed);
  check "map preserves tag, kind and labels"
    (let r = constr_named "P" [ ("x", "A") ] in
     let m = map (fun v -> v ^ "!") r in
     m.tag = r.tag && m.kind = r.kind
     && List.map fst m.fields = List.map fst r.fields
     && lookup (Name "x") m = Some "A!")

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
