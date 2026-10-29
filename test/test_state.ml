open Ts_hoare_logic

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    incr failures;
    Printf.printf "FAIL  %s\n" name)

let check_show name d expected =
  incr total;
  let actual = State.show d in
  if actual <> expected then (
    incr failures;
    Printf.printf "FAIL  %s\n      expected: %s\n      actual:   %s\n" name expected actual)

let box = Ty.record [ ("v", Ty.or_ Ty.string_ Ty.number_) ]

(* --- the degenerate case --------------------------------------------------

   While the heap is Emp a state is an environment written differently. *)

let () =
  check_show "the initial state" State.init "emp";
  check_show "one binding" (State.bind "x" Ty.string_ State.init) "x: string";
  check_show "several bindings"
    (State.init |> State.bind "x" Ty.string_ |> State.bind "b" box)
    {|x: string, b: { %tag: "", v: string | number }|};
  check "lookup finds a binding"
    (State.lookup "x" (State.bind "x" Ty.string_ State.init) = Some Ty.string_);
  check "lookup misses an unbound name" (State.lookup "y" State.init = None);
  check "mem agrees with lookup"
    (State.mem "x" (State.bind "x" Ty.string_ State.init)
    && not (State.mem "y" State.init));
  (* rebinding replaces rather than shadows *)
  check "rebinding replaces"
    (State.lookup "x"
       (State.init |> State.bind "x" Ty.string_ |> State.bind "x" Ty.number_)
    = Some Ty.number_)

(* --- unreachability -------------------------------------------------------

   The empty disjunction is false: no state satisfies it. *)

let () =
  check "the empty disjunction is unreachable" (State.is_unreachable State.unreachable);
  check "the initial state is reachable" (not (State.is_unreachable State.init));
  check_show "false prints as false" State.unreachable "false";
  check "lookup in an unreachable state finds nothing"
    (State.lookup "x" State.unreachable = None);
  (* a binding to an uninhabited type makes the conjunct unreachable *)
  check "an empty binding is pruned"
    (State.is_unreachable (State.prune (State.bind "x" Ty.bot State.init)));
  check "an empty intersection is pruned"
    (State.is_unreachable
       (State.init |> State.bind "x" Ty.string_ |> State.refine "x" Ty.number_))

(* --- narrowing ------------------------------------------------------------

   A passing type test refines a binding; the else-branch refines by the
   complement. Together they are the two halves of a narrowing if. *)

let () =
  let d = State.bind "x" (Ty.or_ Ty.string_ Ty.number_) State.init in
  let then_ = State.refine "x" Ty.string_ d in
  let else_ = State.refine_out "x" Ty.string_ d in
  check "the then-branch narrows"
    (match State.lookup "x" then_ with
    | Some t -> Subty.equiv t Ty.string_
    | None -> false);
  (* the narrower side is kept whole, rather than intersected on each test *)
  check "narrowing does not accumulate"
    (State.show then_ = "x: string");
  check "the else-branch narrows to the complement"
    (match State.lookup "x" else_ with
    | Some t -> Subty.equiv t Ty.number_
    | None -> false);
  (* narrowing a name the state does not bind leaves it alone *)
  check "narrowing an unbound name is a no-op"
    (State.show (State.refine "y" Ty.string_ d) = State.show d);
  (* narrowing to something disjoint makes the branch unreachable *)
  check "an impossible narrowing is unreachable"
    (State.is_unreachable (State.refine "x" Ty.boolean_ d))

(* --- disjunction ----------------------------------------------------------

   Two branches rejoin as a disjunction, and a name bound in both has the union
   of its types. A name bound in only one has no type in the whole state. *)

let () =
  let a = State.bind "x" Ty.string_ State.init in
  let b = State.bind "x" Ty.number_ State.init in
  let joined = State.or_ a b in
  check "a disjunction has two conjuncts" (List.length (State.conjuncts joined) = 2);
  check_show "a disjunction prints with \\/" joined "x: string \\/ x: number";
  check "lookup unions across disjuncts"
    (match State.lookup "x" joined with
    | Some t -> Subty.equiv t (Ty.or_ Ty.string_ Ty.number_)
    | None -> false);
  (* bound in one branch only: the state as a whole says nothing about it *)
  let lopsided = State.or_ (State.bind "y" Ty.string_ State.init) State.init in
  check "a name bound in one branch has no type" (State.lookup "y" lopsided = None);
  (* binding into a disjunction reaches every conjunct *)
  check "binding reaches every conjunct"
    (State.lookup "z" (State.bind "z" Ty.boolean_ joined) = Some Ty.boolean_);
  (* joining with the unreachable state changes nothing *)
  check "false is the identity of \\/"
    (State.show (State.or_ a State.unreachable) = State.show a)

(* --- the shape is ready for the heap --------------------------------------

   Nothing builds a non-empty heap yet, but the representation and its printer
   are in place, so separation types extend this module rather than replace it. *)

let () =
  let c = { State.heap = State.PointsTo ("b", box); bindings = [ (State.var "x", Ty.string_) ]; locs = [] } in
  check_show "a heap assertion prints"
    [ c ]
    {|b |-> { %tag: "", v: string | number } /\ x: string|};
  check_show "separating conjunction prints"
    [ { State.heap = State.Star (State.PointsTo ("a", Ty.string_),
                                 State.PointsTo ("b", Ty.number_));
        bindings = []; locs = [] } ]
    "a |-> string * b |-> number"

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
