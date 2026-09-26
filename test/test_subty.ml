open Ts_hoare_logic
open Ty

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    incr failures;
    Printf.printf "FAIL  %s\n" name)

(* A <: B, and its negation, stated as a table. *)
let sub a b = check (show a ^ " <: " ^ show b) (Subty.subty a b)
let nsub a b = check ("not " ^ show a ^ " <: " ^ show b) (not (Subty.subty a b))
let empty t = check (show t ^ " is empty") (Empty.is_empty t)
let inhabited t = check (show t ^ " is inhabited") (Empty.is_inhabited t)

(* --- the extremes --------------------------------------------------------- *)

let () =
  empty bot;
  inhabited top;
  inhabited string_;
  sub bot string_;
  sub bot top;
  sub string_ top;
  nsub top string_;
  sub top top;
  sub bot bot;
  (* reflexivity is a consequence of set inclusion, not a rule *)
  List.iter (fun t -> sub t t) [ top; bot; string_; number_; str "a"; record [ ("x", string_) ] ]

(* --- primitives and literals ---------------------------------------------- *)

let () =
  nsub string_ number_;
  nsub number_ string_;
  empty (and_ string_ number_);
  empty (and_ string_ boolean_);
  (* a literal is a singleton inside its base type *)
  sub (str "a") string_;
  nsub string_ (str "a");
  sub (num 1.) number_;
  sub (bool_ true) boolean_;
  (* and is disjoint from every other base *)
  empty (and_ (str "a") number_);
  empty (and_ (num 1.) string_);
  (* distinct literals are disjoint *)
  empty (and_ (str "a") (str "b"));
  inhabited (and_ (str "a") (str "a"));
  nsub (str "a") (str "b");
  sub (str "a") (str "a")

(* --- booleans are finite --------------------------------------------------

   string and number have infinitely many values, so removing literals never
   empties them. boolean has exactly two. *)

let () =
  inhabited (diff string_ (str "a"));
  inhabited (diff number_ (num 1.));
  inhabited (diff boolean_ (bool_ true));
  empty (diff boolean_ (or_ (bool_ true) (bool_ false)));
  sub boolean_ (or_ (bool_ true) (bool_ false))

(* --- unions and intersections --------------------------------------------- *)

let () =
  sub string_ (or_ string_ number_);
  sub number_ (or_ string_ number_);
  nsub (or_ string_ number_) string_;
  (* union is commutative as a set operation *)
  sub (or_ string_ number_) (or_ number_ string_);
  sub (or_ number_ string_) (or_ string_ number_);
  (* an intersection is below each side *)
  sub (and_ (or_ string_ number_) string_) string_;
  (* a union of literals *)
  sub (str "a") (or_ (str "a") (str "b"));
  nsub (str "c") (or_ (str "a") (str "b"));
  (* negation *)
  sub (diff (or_ string_ number_) string_) number_;
  empty (and_ string_ (not_ string_));
  inhabited (not_ string_)

(* --- rows: width ----------------------------------------------------------

   An open row means "at least these fields", so a row with more fields is a
   subtype of one with fewer. *)

let () =
  let xa = record [ ("x", string_) ] in
  let xayb = record [ ("x", string_); ("y", number_) ] in
  sub xayb xa;
  nsub xa xayb;
  sub xa (record []);
  nsub (record []) xa

(* --- rows: depth ---------------------------------------------------------- *)

let () =
  sub (record [ ("x", str "a") ]) (record [ ("x", string_) ]);
  nsub (record [ ("x", string_) ]) (record [ ("x", str "a") ]);
  sub (record [ ("x", string_) ]) (record [ ("x", or_ string_ number_) ]);
  (* an empty field empties the row *)
  empty (record [ ("x", bot) ]);
  empty (record [ ("x", and_ string_ number_) ])

(* --- rows: reordering -----------------------------------------------------

   Named fields are order-insensitive, so the two spellings are one type. *)

let () =
  let a = record [ ("x", string_); ("y", number_) ] in
  let b = record [ ("y", number_); ("x", string_) ] in
  sub a b;
  sub b a;
  check "reordering gives the same type" (Subty.equiv a b)

(* --- rows: tokens ---------------------------------------------------------

   Distinct tokens are disjoint. Nominal typing, with no nominal typing rule. *)

let () =
  sub (constr "C" [ string_ ]) (constr "C" [ string_ ]);
  nsub (constr "Dog" [ string_ ]) (constr "Cat" [ string_ ]);
  empty (and_ (constr "Dog" [ string_ ]) (constr "Cat" [ string_ ]));
  (* same shape, different token: unrelated *)
  nsub (constr "C" [ string_ ]) (tuple [ string_ ]);
  nsub (tuple [ string_ ]) (constr "C" [ string_ ]);
  (* a primitive is never a row *)
  empty (and_ string_ (record [ ("x", string_) ]));
  nsub string_ (record [ ("x", string_) ]);
  nsub (record [ ("x", string_) ]) string_

(* --- rows: composite labels -----------------------------------------------

   A composite x@0 answers a demand for x and a demand for 0 alike, so the
   named-positional form refines both the record and the tuple spellings. *)

let () =
  let np = constr_named "P" [ ("x", string_); ("y", number_) ] in
  sub np (constr_record "P" [ ("x", string_) ]);
  sub np (constr_record "P" [ ("y", number_) ]);
  nsub (constr_record "P" [ ("x", string_) ]) np

(* --- discriminated unions -------------------------------------------------

   The shape this project targets. Exhaustiveness and disjointness come from
   the same emptiness test as subtyping (Paper B theorem 4.3). *)

let circle = record [ ("kind", str "circle"); ("r", number_) ]
let square = record [ ("kind", str "square"); ("w", number_) ]
let shape = or_ circle square

let () =
  sub circle shape;
  sub square shape;
  nsub shape circle;
  (* the arms are disjoint, because their discriminants are *)
  empty (and_ circle square);
  check "arms are pairwise disjoint" (Subty.pairwise_disjoint [ circle; square ]);
  check "a repeated arm is not disjoint" (not (Subty.pairwise_disjoint [ circle; circle ]));
  (* exhaustiveness *)
  check "both arms are exhaustive"
    (Subty.exhaustive ~scrutinee:shape ~arms:[ circle; square ]);
  check "one arm is not exhaustive" (not (Subty.exhaustive ~scrutinee:shape ~arms:[ circle ]));
  (* reachability *)
  check "the second arm is reachable"
    (Subty.reachable ~scrutinee:shape ~earlier:[ circle ] ~arm:square);
  check "a repeated arm is unreachable"
    (not (Subty.reachable ~scrutinee:shape ~earlier:[ circle ] ~arm:circle));
  (* narrowing by the discriminant *)
  check "narrowing to circle"
    (Subty.equiv (Subty.refine shape ~by:(record [ ("kind", str "circle") ])) circle);
  check "narrowing away circle"
    (Subty.equiv (Subty.refine_negative shape ~by:(record [ ("kind", str "circle") ])) square)

(* --- the Box type from _refs/ts/testing/test.ts --------------------------- *)

let () =
  let box = record [ ("v", or_ string_ number_) ] in
  let box_str = record [ ("v", string_) ] in
  sub box_str box;
  nsub box box_str;
  (* narrowing b.v to string gives the stronger type *)
  check "narrowing the field" (Subty.equiv (Subty.refine box ~by:box_str) box_str)

(* --- deeply nested finite types ------------------------------------------- *)

let rec nested depth leaf =
  if depth = 0 then leaf else record [ ("x", nested (depth - 1) leaf) ]

let () = empty (nested 150 (and_ string_ number_))

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
