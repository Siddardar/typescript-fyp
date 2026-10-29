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

(* --- logical operators -----------------------------------------------------

   ! gives a boolean. && and || evaluate to one of their operands rather than
   to a boolean, so their type is the union of the two: a && b is a when a is
   falsy, and b otherwise. *)

let () =
  accepts "let a = true; let b = !a;";
  accepts "let a = true; let b: boolean = !a;";
  accepts "let a = true; let b = true; let c = a && b;";
  accepts "let a = true; let b = true; if (a && b) { }";
  accepts "let a = true; if (!a) { } else { }";
  (* the union of the operands, not a boolean *)
  accepts {|let x: number = 1; let s: string = "a"; let r: number | string = x || s;|};
  rejects {|let x: number = 1; let s: string = "a"; let r: number = x || s;|};
  (* operands are still checked *)
  rejects "let a = true; let b = a && undefinedName;";
  rejects "let b = !undefinedName;";
  (* the shape a narrowing condition takes, once narrowing exists *)
  accepts {|function f(x: string | number) { if (typeof x === "string" && true) { } }|};
  accepts {|function f(x: string | number) { if (!(typeof x === "string")) { } }|}

(* --- narrowing a local variable --------------------------------------------

   The surface-level half of Paper A's Match and Cast rules: a condition
   refines the type state along each branch. Sound without ownership, because
   nothing can write a local behind the checker's back.

   A field is a different matter, and is covered further down. *)

let prelude =
  "function wantsString(s: string): number { return 1; }\n\
   function wantsNumber(n: number): number { return 1; }\n"

let p src = prelude ^ src

let () =
  (* the then-branch learns the tested type *)
  accepts (p {|function f(x: string | number) { if (typeof x === "string") { wantsString(x); } }|});
  (* the else-branch learns its complement *)
  accepts
    (p
       {|function f(x: string | number) { if (typeof x === "string") { } else { wantsNumber(x); } }|});
  (* !== swaps the two *)
  accepts (p {|function f(x: string | number) { if (typeof x !== "string") { wantsNumber(x); } }|});
  accepts
    (p {|function f(x: string | number) { if (typeof x !== "string") { } else { wantsString(x); } }|});
  (* so does ! *)
  accepts
    (p {|function f(x: string | number) { if (!(typeof x === "string")) { wantsNumber(x); } }|});
  accepts (p {|function f(x: string | number) { if (!!(typeof x === "string")) { wantsString(x); } }|});
  (* either operand order *)
  accepts (p {|function f(x: string | number) { if ("string" === typeof x) { wantsString(x); } }|});
  (* a three-way union narrows one arm at a time *)
  accepts
    (p
       {|function f(x: string | number | boolean) { if (typeof x === "string") { wantsString(x); } }|});
  (* nested guards compose *)
  accepts
    (p
       {|function f(x: string | number) { if (typeof x === "number") { } else { if (typeof x === "string") { wantsString(x); } } }|})

(* The wrong branch learns the wrong thing. *)
let () =
  rejects (p {|function f(x: string | number) { if (typeof x === "string") { wantsNumber(x); } }|});
  rejects
    (p
       {|function f(x: string | number) { if (typeof x === "string") { } else { wantsString(x); } }|});
  (* and the narrowing does not outlive the branch *)
  rejects (p {|function f(x: string | number) { if (typeof x === "string") { } wantsString(x); }|})

(* --- how conditions compose ------------------------------------------------

   Both halves of an && hold when it holds. When it fails, either could have,
   so nothing is known. || is the mirror. *)

let () =
  accepts
    (p
       {|function f(x: string | number, y: string | number) { if (typeof x === "string" && typeof y === "string") { wantsString(x); wantsString(y); } }|});
  (* a && with an unrelated operand still narrows *)
  accepts
    (p {|function f(x: string | number) { if (typeof x === "string" && true) { wantsString(x); } }|});
  (* || proves nothing in the then-branch *)
  rejects
    (p {|function f(x: string | number) { if (typeof x === "string" || true) { wantsString(x); } }|});
  (* but it does in the else-branch, where both halves failed *)
  accepts
    (p
       {|function f(x: string | number) { if (typeof x === "string" || false) { } else { wantsNumber(x); } }|});
  (* and && is the mirror: its else-branch proves nothing *)
  rejects
    (p
       {|function f(x: string | number) { if (typeof x === "string" && true) { } else { wantsNumber(x); } }|})

(* --- what does not narrow -------------------------------------------------- *)

let () =
  (* A field narrows like a variable, since the state can hold a fact about a
     path. What it cannot survive is a call — see below. *)
  accepts
    (p
       {|type B = { v: string | number }
function f(b: B) { if (typeof b.v === "string") { wantsString(b.v); } }|});
  (* object and function have no single type in the kernel, so a test against
     either narrows nothing *)
  rejects
    (p
       {|type B = { v: string }
function f(x: string | B) { if (typeof x === "object") { } else { wantsString(x); } }|});
  (* a condition that is not a type test proves nothing *)
  rejects (p {|function f(x: string | number) { if (true) { wantsString(x); } }|})

(* --- unreachable branches --------------------------------------------------

   A refinement that empties the binding makes the branch dead, so its body is
   skipped rather than checked against a state that says nothing. *)

let () =
  accepts {|function f(x: string) { if (typeof x === "number") { let q = undefinedName; } }|};
  accepts
    {|function f(x: string) { if (typeof x === "string") { } else { let q = undefinedName; } }|};
  (* the live branch is still checked *)
  rejects {|function f(x: string) { if (typeof x === "string") { let q = undefinedName; } }|}

(* --- a call invalidates what it writes --------------------------------------

   A signature says what a function returns, not what it changes, so the
   effects are read off each body: the paths it writes, named by parameter.
   A caller substitutes its arguments and invalidates only those, plus
   anything that could be the same location.

   These two programs differ by one line, and now get different verdicts.

     tsc --strict    accepts both; the second is the one that throws
     this checker    accepts the first, rejects the second

   What remains imprecise is aliasing: two paths with compatible field chains
   may be rooted at the same object, so both go. Ownership is what turns "may
   be" into "is not". *)

let safe =
  p
    {|type Box = { v: string | number }
function f(b: Box) {
  if (typeof b.v === "string") {
    wantsString(b.v);
  }
}|}

let unsound =
  p
    {|type Box = { v: string | number }
function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  if (typeof b.v === "string") {
    mutate(b);
    wantsString(b.v);
  }
}|}

let () =
  accepts safe;
  rejects unsound;
  (* the write itself also invalidates, without any call involved *)
  rejects
    (p
       {|type Box = { v: string | number }
function f(b: Box) {
  if (typeof b.v === "string") {
    b.v = 42;
    wantsString(b.v);
  }
}|});
  (* an alias makes no difference: any call drops the refinement, whether or
     not the object is passed. That is what keeps this sound, and it is the
     case a passing-based rule would get wrong. *)
  rejects
    (p
       {|type Box = { v: string | number }
function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  let g = b;
  if (typeof b.v === "string") {
    mutate(g);
    wantsString(b.v);
  }
}|})

(* A call that writes nothing costs nothing: the callee's effects are read off
   its body, so only what it actually writes is invalidated. *)
let () =
  accepts
    (p
       {|type Box = { v: string | number }
function harmless(): number { return 1; }
function f(b: Box) {
  if (typeof b.v === "string") {
    harmless();
    wantsString(b.v);
  }
}|});
  (* but arguments are evaluated before the call, so the refinement still
     holds while they are read *)
  accepts
    (p
       {|type Box = { v: string | number }
function f(b: Box) {
  if (typeof b.v === "string") {
    wantsString(b.v);
  }
}|});
  (* a local variable is unaffected: only fields are dropped *)
  accepts
    (p
       {|function harmless(): number { return 1; }
function f(x: string | number) {
  if (typeof x === "string") {
    harmless();
    wantsString(x);
  }
}|})

(* --- effects are read off the body -----------------------------------------

   A function's writes are inferred, not declared. Paper A supplies them in a
   specification and lists inference as future work; requiring an annotation
   on every function would make this unusable on ordinary TypeScript. *)

let () =
  (* a write through a local alias inside the callee still counts *)
  rejects
    (p
       {|type Box = { v: string | number }
function mutate(b: Box) { let c = b; c.v = 42; }
function f(b: Box) {
  if (typeof b.v === "string") { mutate(b); wantsString(b.v); }
}|});
  (* and so does one reached through another call *)
  rejects
    (p
       {|type Box = { v: string | number }
function inner(b: Box) { b.v = 42; }
function outer(b: Box) { inner(b); }
function f(b: Box) {
  if (typeof b.v === "string") { outer(b); wantsString(b.v); }
}|});
  (* a function that writes a DIFFERENT field leaves this one alone *)
  accepts
    (p
       {|type Box = { v: string | number; w: string | number }
function mutate(b: Box) { b.w = 42; }
function f(b: Box) {
  if (typeof b.v === "string") { mutate(b); wantsString(b.v); }
}|});
  (* writing into a value the callee built itself is invisible here *)
  accepts
    (p
       {|type Box = { v: string | number }
function makes(): number { let o: Box = { v: 1 }; o.v = 2; return 1; }
function f(b: Box) {
  if (typeof b.v === "string") { makes(); wantsString(b.v); }
}|});
  (* recursion terminates, and its effects are still found *)
  rejects
    (p
       {|type Box = { v: string | number }
function loop(b: Box, n: number) { b.v = 42; loop(b, n); }
function f(b: Box) {
  if (typeof b.v === "string") { loop(b, 1); wantsString(b.v); }
}|});
  (* so does mutual recursion *)
  rejects
    (p
       {|type Box = { v: string | number }
function ping(b: Box) { pong(b); }
function pong(b: Box) { b.v = 42; ping(b); }
function f(b: Box) {
  if (typeof b.v === "string") { ping(b); wantsString(b.v); }
}|});
  (* console.log writes nothing *)
  accepts
    (p
       {|type Box = { v: string | number }
function f(b: Box) {
  if (typeof b.v === "string") { console.log(1); wantsString(b.v); }
}|})

(* --- a direct write invalidates possible aliases ---------------------------

   No call is involved here. c and b may be the same object, so writing c.v
   has to invalidate b.v. *)

let () =
  rejects
    (p
       {|type Box = { v: string | number }
function f(b: Box) {
  let c = b;
  if (typeof b.v === "string") { c.v = 42; wantsString(b.v); }
}|});
  (* a write to a different field cannot collide *)
  accepts
    (p
       {|type Box = { v: string | number; w: string | number }
function f(b: Box) {
  let c = b;
  if (typeof b.v === "string") { c.w = 42; wantsString(b.v); }
}|})

(* --- abstract locations ----------------------------------------------------

   Each variable denotes an object, as far as the checker can tell. A value
   built here is nobody else's; a plain copy is the same object; anything of
   unknown provenance may be anything. Two variables with different known
   locations cannot collide, so a write through one leaves the other alone. *)

let q src = p ("type Box = { v: string | number }\n" ^ src)

let () =
  (* freshly built, so it cannot be b *)
  accepts
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  let c: Box = { v: 1 };
  if (typeof b.v === "string") { mutate(c); wantsString(b.v); }
}|});
  (* a copy IS b *)
  rejects
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  let c = b;
  if (typeof b.v === "string") { mutate(c); wantsString(b.v); }
}|});
  (* distinct parameters are assumed distinct, discharged at each call *)
  accepts
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box, c: Box) {
  if (typeof b.v === "string") { mutate(c); wantsString(b.v); }
}|});
  (* a value of unknown provenance may be anything *)
  rejects
    (q
       {|function id(x: Box): Box { return x; }
function f(b: Box) {
  let c = id(b);
  if (typeof b.v === "string") { c.v = 42; wantsString(b.v); }
}|});
  (* the same distinctions apply to a direct write *)
  accepts
    (q
       {|function f(b: Box) {
  let c: Box = { v: 1 };
  if (typeof b.v === "string") { c.v = 42; wantsString(b.v); }
}|});
  rejects
    (q
       {|function f(b: Box) {
  let c = b;
  if (typeof b.v === "string") { c.v = 42; wantsString(b.v); }
}|})

(* --- the separation obligation at a call -----------------------------------

   A body assumes its parameters are distinct objects. Each call has to show
   they are, which is Paper A's req b |-> T * c |-> U with the obligation
   moved from a written precondition to a checked call site.

   Only positions the callee writes matter: two arguments it never writes
   through may safely be the same thing. *)

let () =
  (* the hole phase 1 would otherwise leave: f relies on b and c being
     separate, and this call breaks that *)
  rejects
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box, c: Box) {
  if (typeof b.v === "string") { mutate(c); wantsString(b.v); }
}
function caller(x: Box) { f(x, x); }|});
  rejects (q {|function two(b: Box, c: Box) { c.v = 42; }
function caller(x: Box) { two(x, x); }|});
  (* a copy is the same object, so it fails the same way *)
  rejects (q {|function two(b: Box, c: Box) { c.v = 42; }
function caller(x: Box) { let g = x; two(x, g); }|});
  (* distinct arguments are fine *)
  accepts (q {|function two(b: Box, c: Box) { c.v = 42; }
function caller(x: Box, y: Box) { two(x, y); }|});
  (* so is a freshly built one *)
  accepts (q {|function two(b: Box, c: Box) { c.v = 42; }
function caller(x: Box) { let f: Box = { v: 1 }; two(x, f); }|});
  (* a callee that writes nothing imposes no obligation *)
  accepts (q {|function reads(b: Box, c: Box): number { return 1; }
function caller(x: Box) { reads(x, x); }|})

(* --- strong update ---------------------------------------------------------

   Where the callee's write always happens and the type it leaves is known,
   the caller records that type instead of falling back to the declared one.
   Only an owner may say this, which is what the separation obligation
   establishes. *)

let () =
  (* the case BOTH this checker and tsc previously got wrong: tsc thinks b.v
     is still a string, and dropping to the declared type is no better *)
  accepts
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  if (typeof b.v === "string") { mutate(b); wantsNumber(b.v); }
}|});
  (* and it is no longer a string *)
  rejects
    (q
       {|function mutate(b: Box) { b.v = 42; }
function f(b: Box) {
  if (typeof b.v === "string") { mutate(b); wantsString(b.v); }
}|});
  (* a direct write is the same *)
  accepts
    (q
       {|function f(b: Box) {
  if (typeof b.v === "string") { b.v = 42; wantsNumber(b.v); }
}|});
  (* a write that may not run must NOT be claimed: the old value may survive *)
  rejects
    (q
       {|function maybe(b: Box, c: boolean) { if (c) { b.v = 42; } }
function f(b: Box, c: boolean) {
  if (typeof b.v === "string") { maybe(b, c); wantsNumber(b.v); }
}|});
  (* nor may one whose type cannot be read off the expression *)
  rejects
    (q
       {|function gives(): string | number { return 1; }
function opaque(b: Box) { b.v = gives(); }
function f(b: Box) {
  if (typeof b.v === "string") { opaque(b); wantsNumber(b.v); }
}|})

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
