(* The emptiness test

   A type denotes a set of values ->  answers: is set empty? 
   Because the type language has complement, five separate static
   questions reduce to this one test:

     A <: B              is A & !B empty?
     match exhaustive    is Scrutinee & !(arm1 | ... | armN) empty?
     arm reachable       is the arm's guard non-empty?
     flow refinement     is the refined type empty?
     inhabited           directly
   *)

(* disjunctive normal form -> list of positive and negative types
   whole type is empty when all disjuncts are empty *)
type disjunct = { pos : Ty.t list; neg : Ty.t list }

(* flatten types into a list of disjunct
    e.g. (string | number) & !boolean -> (string & !boolean) | (number & !boolean)
    => { pos = [string]; neg = [boolean] }; { pos = [number]; neg = [boolean] }
*)
let rec dnf (t : Ty.t) : disjunct list =
  match t with
  | Ty.Bot -> []  (* no disjuncts *)
  | Ty.Top -> [ { pos = []; neg = [] } ]  (* one disjunct, unconstrained *)
  | Ty.Or (a, b) -> dnf a @ dnf b
  | Ty.And (a, b) ->
      (* distribute: every pairing of a disjunct from each side *)
      List.concat_map
        (fun d1 ->
          List.map (fun d2 -> { pos = d1.pos @ d2.pos; neg = d1.neg @ d2.neg }) (dnf b))
        (dnf a)
  | Ty.Not a -> (
      match a with
      | Ty.Bot -> [ { pos = []; neg = [] } ]
      | Ty.Top -> []
      | Ty.Not b -> dnf b
      | Ty.And (x, y) -> dnf (Ty.Or (Ty.Not x, Ty.Not y))
      | Ty.Or (x, y) -> dnf (Ty.And (Ty.Not x, Ty.Not y))
      | atom -> [ { pos = []; neg = [ atom ] } ])
  | atom -> [ { pos = [ atom ]; neg = [] } ]

(* --- primitives ---------------------------------------------------------- *)

type prim = PBase of Ty.base | PLit of Ty.lit

let to_prim = function
  | Ty.Base b -> Some (PBase b)
  | Ty.Lit l -> Some (PLit l)
  | _ -> None

let to_row = function Ty.Row r -> Some r | _ -> None

(* A literal inhabits exactly one base type, so intersecting a base with a
   literal keeps the literal when they agree and is empty otherwise. *)
let inter_prim a b =
  match (a, b) with
  | PBase x, PBase y -> if x = y then Some a else None
  | PBase x, PLit l | PLit l, PBase x -> if Ty.base_of_lit l = x then Some (PLit l) else None
  | PLit l, PLit m -> if l = m then Some a else None

(* Is the positive primitive constraint entirely covered by the negatives? *)
let prim_covered p negs =
  match p with
  | PLit l ->
      List.exists
        (function PLit m -> m = l | PBase b -> b = Ty.base_of_lit l)
        negs
  | PBase b ->
      List.exists (fun n -> n = PBase b) negs
      (* boolean has exactly two values, so removing both empties it; string
         and number are infinite, so removing literals never does *)
      || b = Ty.Boolean
         && List.mem (PLit (Ty.LBool true)) negs
         && List.mem (PLit (Ty.LBool false)) negs

(* --- row constraints -----------------------------------------------------

   Intersecting rows, and subtracting rows from them, needs one thing a row
   type cannot express: a label required to be ABSENT. That is what
   distinguishes {x:A} from {x:A,y:B} — the first permits a value with no y,
   and subtracting the second leaves exactly those values. *)

type row_c = {
  tag : Row.token;
  closed : bool;  (* the domain is exactly [present], with no extra labels *)
  present : (Row.label * Ty.t) list;
  absent : Row.label list;
}

(* Two labels conflict when either answers the other: x@0 collides with both
   a bare x and a bare 0. *)
let label_conflict a b = Row.answers a b || Row.answers b a

(* When two labels conflict, the composite is the more informative spelling. *)
let merge_label a b =
  match (a, b) with Row.Composite _, _ -> a | _, Row.Composite _ -> b | _ -> a

let find_field l present =
  List.find_map (fun (l', t) -> if label_conflict l' l then Some t else None) present

let set_field c l t =
  let matching, rest = List.partition (fun (l', _) -> label_conflict l' l) c.present in
  let label = match matching with (l', _) :: _ -> merge_label l' l | [] -> l in
  { c with present = (label, t) :: rest }

let row_to_c (r : Ty.t Row.t) =
  {
    tag = r.Row.tag;
    closed = r.Row.kind = Row.Closed;
    present = r.Row.fields;
    absent = [];
  }

(* Intersect a constraint with another row of the same token. Returns None when
   the result is empty for a structural reason. *)
let inter_row c (r : Ty.t Row.t) =
  if c.tag <> r.Row.tag then None  (* distinct tokens are disjoint *)
  else
    let r_closed = r.Row.kind = Row.Closed in
    let missing_from from_fields label =
      not (List.exists (fun (l, _) -> label_conflict l label) from_fields)
    in
    (* a closed side admits no label the other requires but it lacks *)
    if c.closed && List.exists (fun (l, _) -> missing_from c.present l) r.Row.fields then None
    else if r_closed && List.exists (fun (l, _) -> missing_from r.Row.fields l) c.present then
      None
    else
      Some
        (List.fold_left
           (fun acc (l, t) ->
             match find_field l acc.present with
             | Some existing -> set_field acc l (Ty.and_ existing t)
             | None -> { acc with present = (l, t) :: acc.present })
           { c with closed = c.closed || r_closed }
           r.Row.fields)

(* --- the decision procedure ----------------------------------------------

   Elaboration rejects recursive aliases, so every core type is finite.
   Recursive field checks descend into nested field types, while row
   subtraction consumes one negative row at each step. *)

let rec is_empty t = List.for_all disjunct_empty (dnf t)

and disjunct_empty d =
  if List.mem Ty.Bot d.pos then true
  else if List.mem Ty.Top d.neg then true  (* everything is subtracted *)
  else
    let pos = List.filter (fun t -> t <> Ty.Top) d.pos in
    let prims_pos = List.filter_map to_prim pos in
    let rows_pos = List.filter_map to_row pos in
    let prims_neg = List.filter_map to_prim d.neg in
    let rows_neg = List.filter_map to_row d.neg in
    (* a value is a primitive or a row, never both *)
    if prims_pos <> [] && rows_pos <> [] then true
    else if prims_pos <> [] then
      match
        List.fold_left
          (fun acc p -> Option.bind acc (fun a -> inter_prim a p))
          (Some (List.hd prims_pos))
          (List.tl prims_pos)
      with
      | None -> true
      | Some p -> prim_covered p prims_neg
    else if rows_pos <> [] then
      match
        List.fold_left
          (fun acc r -> Option.bind acc (fun c -> inter_row c r))
          (Some (row_to_c (List.hd rows_pos)))
          (List.tl rows_pos)
      with
      | None -> true
      | Some c -> row_diff_empty c rows_neg
    else
      (* No positive constraint, so the disjunct is everything minus the
         negatives. Covering everything needs Top, handled above. *)
      false

(* A constraint is empty when a field is empty, or a label is required both
   present and absent. *)
and row_c_empty c =
  List.exists (fun (_, t) -> is_empty t) c.present
  || List.exists
       (fun a -> List.exists (fun (l, _) -> label_conflict l a) c.present)
       c.absent

(* c minus the negative rows.

   A value is outside a row type n when some label of n is missing from it, or
   the value at that label is outside n's type there. So

     c \ n  =  union over labels L of n of
                 (c with L absent)  union  (c with L refined by !n(L))

   and c \ n is empty exactly when every one of those branches is. Subtracting
   the remaining negatives distributes over the union. *)
and row_diff_empty c negs =
  if row_c_empty c then true
  else
    match negs with
    | [] -> false  (* inhabited, and nothing left to subtract *)
    | n :: rest ->
        let n_closed = n.Row.kind = Row.Closed in
        let lacks fields label =
          not (List.exists (fun (l, _) -> label_conflict l label) fields)
        in
        let covers_nothing =
          (* a different token: disjoint *)
          c.tag <> n.Row.tag
          (* n forbids extra labels, c permits them: c has values n cannot hold *)
          || (n_closed && not c.closed)
          (* c is closed and lacks a label n requires *)
          || (c.closed && List.exists (fun (l, _) -> lacks c.present l) n.Row.fields)
          (* both closed, and c has a label n forbids *)
          || (c.closed && n_closed && List.exists (fun (l, _) -> lacks n.Row.fields l) c.present)
        in
        if covers_nothing then row_diff_empty c rest
        else
          List.for_all
            (fun (nl, nt) ->
              let absent_branch = { c with absent = nl :: c.absent } in
              let refined_branch =
                match find_field nl c.present with
                | Some t -> set_field c nl (Ty.and_ t (Ty.not_ nt))
                | None -> { c with present = (nl, Ty.not_ nt) :: c.present }
              in
              row_diff_empty absent_branch rest && row_diff_empty refined_branch rest)
            n.Row.fields

let is_inhabited t = not (is_empty t)
