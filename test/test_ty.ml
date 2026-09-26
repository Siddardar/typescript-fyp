open Ts_hoare_logic
open Ty

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    incr failures;
    Printf.printf "FAIL  %s\n" name)

let check_show name t expected =
  incr total;
  let actual = show t in
  if actual <> expected then (
    incr failures;
    Printf.printf "FAIL  %s\n      expected: %s\n      actual:   %s\n" name expected actual)

(* --- smart constructors normalise as they build ---------------------------

   The obvious redundancies never enter the tree, so the emptiness test has
   less to do. *)

let () =
  (* absorbing and identity elements *)
  check "bot absorbs under &" (and_ bot string_ = bot && and_ string_ bot = bot);
  check "top is the identity of &" (and_ top string_ = string_ && and_ string_ top = string_);
  check "top absorbs under |" (or_ top string_ = top && or_ string_ top = top);
  check "bot is the identity of |" (or_ bot string_ = string_ && or_ string_ bot = string_);
  (* idempotence *)
  check "a & a = a" (and_ string_ string_ = string_);
  check "a | a = a" (or_ string_ string_ = string_);
  (* negation of the extremes *)
  check "!unknown = never" (not_ top = bot);
  check "!never = unknown" (not_ bot = top);
  check "!!a = a" (not_ (not_ string_) = string_);
  (* a genuine pair is left alone *)
  check "a & b is kept" (and_ string_ number_ = And (string_, number_));
  check "a | b is kept" (or_ string_ number_ = Or (string_, number_))

(* --- negation is pushed to the leaves -------------------------------------

   De Morgan is applied on construction, so a negation never sits above a
   connective. The emptiness test can then assume negations reach only atoms. *)

let () =
  check "!(a & b) = !a | !b" (not_ (and_ string_ number_) = Or (Not string_, Not number_));
  check "!(a | b) = !a & !b" (not_ (or_ string_ number_) = And (Not string_, Not number_));
  check "negation reaches the leaves through nesting"
    (not_ (or_ (and_ string_ number_) boolean_)
    = And (Or (Not string_, Not number_), Not boolean_))

(* --- folds ---------------------------------------------------------------- *)

let () =
  check "any_of [] is never" (any_of [] = bot);
  check "all_of [] is unknown" (all_of [] = top);
  check "any_of one" (any_of [ string_ ] = string_);
  check "all_of one" (all_of [ string_ ] = string_);
  check "any_of drops never" (any_of [ bot; string_; bot ] = string_);
  check "all_of drops unknown" (all_of [ top; string_; top ] = string_);
  check "diff is a & !b" (diff string_ number_ = And (string_, Not number_));
  check "a & !a is never" (and_ string_ (not_ string_) = bot);
  check "a | !a is unknown" (or_ string_ (not_ string_) = top);
  check "a \\ a is never" (diff string_ string_ = bot);
  check "a \\ never is a" (diff string_ bot = string_);
  check "a \\ unknown is never" (diff string_ top = bot)

(* --- literals -------------------------------------------------------------

   A literal is a singleton, and inhabits exactly one base type. That is what
   will make "circle" & number empty. *)

let () =
  check "string literals" (base_of_lit (LStr "a") = String);
  check "number literals" (base_of_lit (LNum 1.) = Number);
  check "boolean literals" (base_of_lit (LBool true) = Boolean);
  check "distinct literals differ" (str "a" <> str "b");
  check "equal literals are equal" (str "a" = str "a")

(* --- printing -------------------------------------------------------------

   Precedence-aware, not fully parenthesised: ! binds tightest, then &, then |.
   Base types use their TypeScript spelling, since these strings reach
   diagnostics. *)

let () =
  check_show "unknown" top "unknown";
  check_show "never" bot "never";
  check_show "base" string_ "string";
  check_show "string literal" (str "circle") {|"circle"|};
  check_show "number literal" (num 42.) "42";
  check_show "boolean literal" (bool_ true) "true";
  check_show "union" (or_ string_ number_) "string | number";
  check_show "intersection" (and_ string_ number_) "string & number";
  check_show "negation of an atom" (Not string_) "!string";
  (* & binds tighter than |, so no parentheses are needed here *)
  check_show "and inside or" (Or (And (string_, number_), boolean_))
    "string & number | boolean";
  (* but | inside & needs them *)
  check_show "or inside and" (And (Or (string_, number_), boolean_))
    "(string | number) & boolean";
  check_show "negation of a connective" (Not (Or (string_, number_)))
    "!(string | number)"

(* --- rows as types --------------------------------------------------------

   The four surface vocabularies, now carrying types rather than values. *)

let () =
  check_show "record" (record [ ("v", or_ string_ number_) ])
    {|{ %tag: "", v: string | number }|};
  check_show "tuple" (tuple [ string_; number_ ]) {|{ %tag: "", 0: string, 1: number }_c|};
  check_show "constructor" (constr "Cons" [ string_ ]) "{ %tag: tok(Cons), 0: string }_c";
  check_show "named-positional" (constr_named "Point" [ ("x", number_) ])
    "{ %tag: tok(Point), x@0: number }_c";
  check_show "unit" unit_ {|{ %tag: "" }_c|};
  (* a discriminated union, the shape the project targets *)
  check_show "discriminated union"
    (or_
       (record [ ("kind", str "circle"); ("r", number_) ])
       (record [ ("kind", str "square"); ("w", number_) ]))
    {|{ %tag: "", kind: "circle", r: number } | { %tag: "", kind: "square", w: number }|};
  (* the Box type from _refs/ts/testing/test.ts *)
  check_show "Box" (record [ ("v", or_ string_ number_) ])
    {|{ %tag: "", v: string | number }|}

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
