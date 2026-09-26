(* Subtyping: A <: B iff Set(A) subset Set(B) iff A & !B is empty. *)

let ( <: ) a b = Empty.is_empty (Ty.diff a b)
let subty = ( <: ) (* for testing *)

(* other checkers mentioned in the paper *)
let equiv a b = a <: b && b <: a

(* do arms handle every possible input? *)
let exhaustive ~scrutinee ~arms = scrutinee <: Ty.any_of arms

(* Can this arm ever be taken, given what earlier arms already matched? -> depends on arm order*)
let reachable ~scrutinee ~earlier ~arm =
  Empty.is_inhabited (Ty.and_ (Ty.diff scrutinee (Ty.any_of earlier)) arm)

(* narrow a type by a test, as an if-branch does. *)
let refine t ~by = Ty.and_ t by
let refine_negative t ~by = Ty.diff t by

(* guards pairwise disjoint? *)
let pairwise_disjoint ts =
  let rec go = function
    | [] -> true
    | t :: rest ->
        List.for_all (fun u -> Empty.is_empty (Ty.and_ t u)) rest && go rest
  in
  go ts
