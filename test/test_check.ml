open Ts_hoare_logic

let failures = ref 0
let total = ref 0

let run src = Check.run (Parser.of_string src)

let accepts src =
  incr total;
  match run src with
  | Ok () -> ()
  | Error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      should be accepted, but: %s\n" src msg

let rejects src =
  incr total;
  match run src with
  | Error _ -> ()
  | Ok () ->
      incr failures;
      Printf.printf "FAIL  %S\n      should be rejected\n" src

(* --- literals, bindings, and annotations ---------------------------------- *)

let () =
  accepts "let x = 1;";
  accepts {|let x = "a";|};
  accepts "let x: number = 1;";
  accepts "let x: string | number = 1;";
  (* an annotation is checked against and then bound, so the declaration stays
     as wide as it was written *)
  accepts "let x: string | number = 1; let y: string | number = x;";
  rejects {|let x: number = "a";|};
  rejects "let x: string = 1;";
  rejects "let x = y;";
  (* a later statement sees what an earlier one bound *)
  accepts "let x = 1; let y = x;";
  rejects "let y = x; let x = 1;"

(* --- object literals and field reads -------------------------------------- *)

let () =
  accepts "let o = { a: 1 };";
  accepts "let o = { a: 1 }; let n = o.a;";
  accepts {|let o = { a: 1, b: "s" }; let s = o.b;|};
  accepts "let o = { a: { b: 1 } }; let n = o.a.b;";
  rejects "let o = { a: 1 }; let n = o.b;";
  rejects "let x = 1; let n = x.a;";
  (* a field read distributes over a union only when every arm has the field *)
  accepts
    "type A = { k: number } type B = { k: string } type AB = A | B\n\
     function f(x: AB) { let v = x.k; }";
  rejects
    "type A = { k: number } type B = { j: string } type AB = A | B\n\
     function f(x: AB) { let v = x.k; }"

(* --- calls ----------------------------------------------------------------- *)

let () =
  accepts "function f(x: number): number { return 1; } let n = f(1);";
  accepts "function f(): number { return 1; } let n = f();";
  (* an argument is checked against the parameter, so a subtype is fine *)
  accepts "function f(x: string | number): number { return 1; } let n = f(1);";
  rejects {|function f(x: number): number { return 1; } let n = f("a");|};
  rejects "function f(x: number): number { return 1; } let n = f(1, 2);";
  rejects "function f(x: number): number { return 1; } let n = f();";
  rejects "let x = 1; let y = x(1);";
  (* mutual recursion works, since every signature is collected first *)
  accepts
    "function f(x: number): number { return g(x); }\n\
     function g(x: number): number { return f(x); }"

(* --- returns --------------------------------------------------------------- *)

let () =
  accepts "function f(): number { return 1; }";
  accepts "function f(): string | number { return 1; }";
  rejects {|function f(): number { return "a"; }|};
  rejects "return 1;"

(* --- assignment ------------------------------------------------------------

   A write must stay within the target's declared type. Nothing narrows: a
   pure type cannot be mutated to a different type, which is exactly what
   separation types will relax. *)

let () =
  accepts "type B = { v: string | number }\nfunction f(b: B) { b.v = 1; }";
  accepts {|type B = { v: string | number }
function f(b: B) { b.v = "a"; }|};
  rejects "type B = { v: string }\nfunction f(b: B) { b.v = 1; }";
  rejects "type B = { v: string }\nfunction f(b: B) { b.w = 1; }";
  rejects "function f(x: number) { y = 1; }"
  (* a non-lvalue on the left of '=' is rejected by the parser, so it never
     reaches the checker *)

(* --- nested function declarations -----------------------------------------

   A nested declaration is checked where it appears, and its name is bound both
   after it and inside its own body, so recursion works. Before this, [stmt]
   ignored FunctionDecl entirely: the body was never visited and the name was
   never bound, so the checker reported ok about code it had not read. *)

let () =
  accepts "function f() { function g(): number { return 1; } }";
  accepts "function f() { function g(): number { return 1; } let n = g(); }";
  (* recursion: the name is in scope inside its own body *)
  accepts "function f() { function g(x: number): number { return g(x); } }";
  (* the body really is checked *)
  rejects {|function f() { function g(): number { return "a"; } }|};
  rejects "function f() { function g(x: number): number { return 1; } let n = g(\"a\"); }";
  (* and the name does not escape the enclosing body *)
  rejects "function f() { function g(): number { return 1; } }\nlet n = g();";
  (* nesting more than one deep *)
  accepts
    "function f() { function g() { function h(): number { return 1; } let n = h(); } }";
  rejects
    {|function f() { function g() { function h(): number { return "a"; } } }|}

(* --- every path must return -----------------------------------------------

   An annotated result must actually be produced. An omitted annotation becomes
   unknown, which nothing is required to produce: a stand-in for void, which
   the kernel cannot express yet. *)

let () =
  accepts "function f(x: number): number { return 1; }";
  accepts "function f(x: number): number { if (x) { return 1; } else { return 2; } }";
  (* a return after the if covers every path *)
  accepts "function f(x: number): number { if (x) { } return 1; }";
  rejects "function f(): number { }";
  (* one branch returning is not enough: the else path falls through *)
  rejects "function f(x: number): number { if (x) { return 1; } }";
  rejects "function f(x: number): number { if (x) { return 1; } else { } }";
  (* a bare return produces nothing, so it cannot satisfy a result type *)
  rejects "function f(): number { return; }";
  (* without an annotation there is nothing to produce *)
  accepts "function f() { }";
  accepts "function f() { return 1; }";
  accepts "function f() { return; }";
  (* the rule applies to nested declarations too *)
  rejects "function f() { function g(): number { } }"

(* --- scoping ---------------------------------------------------------------

   A binding made inside a block does not escape it. *)

let () =
  accepts "function f() { let x = 1; }";
  accepts "function f() { { let x = 1; } }";
  rejects "function f() { { let x = 1; } let y = x; }";
  (* nor does a parameter escape its function *)
  rejects "function f(x: number) {}\nlet y = x;"

(* --- the shortcoming -------------------------------------------------------

   This layer is flow-INSENSITIVE. An [if] checks both branches against the
   incoming state and discards whatever its condition proved, so a narrowing
   guard buys nothing. These two programs differ by one line — a call that
   invalidates the narrowing — and this checker gives them the same verdict.

     tsc --strict    accepts both; the second throws at runtime
     this checker    rejects both
     the goal        accept the first, reject the second

   Increment 2 adds the rules that refine the state, which makes the first
   pass. Increment 3 adds separation types, which keeps the second rejected. *)

let safe =
  {|type Box = { v: string | number }
function wantsString(s: string): number { return 1; }
function g(b: Box) {
  if (typeof b.v === "string") {
    wantsString(b.v);
  }
}|}

let unsound =
  {|type Box = { v: string | number }
function wantsString(s: string): number { return 1; }
function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  if (typeof b.v === "string") {
    mutate(b);
    wantsString(b.v);
  }
}|}

let () =
  rejects safe;
  rejects unsound;
  incr total;
  (* and for the same reason, which is the point *)
  (match (run safe, run unsound) with
  | Error a, Error b when a = b -> ()
  | Error a, Error b ->
      incr failures;
      Printf.printf "FAIL  the two programs are rejected differently\n  %s\n  %s\n" a b
  | _ ->
      incr failures;
      Printf.printf "FAIL  both programs should be rejected\n");
  (* without the guard, the same call is rejected identically: the guard is
     doing nothing at all *)
  rejects
    {|type Box = { v: string | number }
function wantsString(s: string): number { return 1; }
function g(b: Box) { wantsString(b.v); }|}

(* --- conditions and typeof ------------------------------------------------- *)

let () =
  accepts "let x = 1; if (x) { let y = 1; }";
  accepts {|let x = 1; let t = typeof x;|};
  (* typeof reads the tags a value of that type can answer with *)
  accepts {|let x = 1; let t: "number" = typeof x;|};
  rejects {|let x = 1; let t: "string" = typeof x;|};
  accepts {|function f(x: string | number) { let t: "string" | "number" = typeof x; }|};
  accepts "let x = 1; if (typeof x === \"number\") { let y = 1; } else { let z = 2; }"

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
