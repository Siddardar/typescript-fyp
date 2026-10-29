(* --- heap assertions ------------------------------------------------------
   who owns what memory
   Unused while the checker is flow-insensitive *)

type heap =
  | Emp  (* no cell is owned *)
  | PointsTo of string * Ty.t  (* x |-> t: owned exclusively, holding a t *)
  | Star of heap * heap

(* --- states ---------------------------------------------------------------
   TODO: existential quantification. each conjunct as
   exists v*. sigma /\ pi; fresh result variables will need it at entailment. *)

(* --- paths ---------------------------------------------------------------
   allow fields of record to have a type *)

type path = { root : string; fields : string list }

let var name = { root = name; fields = [] }
let field p f = { p with fields = p.fields @ [ f ] }
let is_var p = p.fields = []
let show_path p = String.concat "." (p.root :: p.fields)

(* --- abstract locations ---------------------------------------------------

   Which object a variable denotes, as far as the checker can tell. Two
   variables with different known locations cannot be the same object, so a
   write through one leaves the other's refinements alone.

   [None] means "could be anything", which is the conservative answer and is
   what a value of unknown provenance gets.

   Distinct parameters are given distinct locations on entry. That is an
   ASSUMPTION about the caller, discharged at each call site: see the
   separation obligation in Check. A function nobody calls keeps an unchecked
   assumption, which is the usual caveat of reasoning about one function at a
   time. *)

type loc = int

let next_loc = ref 0

let fresh_loc () =
  incr next_loc;
  !next_loc

type conjunct = {
  heap : heap;
  bindings : (path * Ty.t) list;
  (* the object each variable denotes; absent means unknown *)
  locs : (string * loc) list;
}

(* A disjunction. The empty list is false: no state satisfies it, so the
   program point is unreachable. *)
type t = conjunct list

let unreachable : t = []
let is_unreachable (d : t) = d = []
let init : t = [ { heap = Emp; bindings = []; locs = [] } ]
let conjuncts (d : t) = d

let prune (d : t) =
  List.filter (fun c -> not (List.exists (fun (_, t) -> Empty.is_empty t) c.bindings)) d

let or_ (a : t) (b : t) : t = a @ b

(* --- bindings ------------------------------------------------------------- *)

(* Binding a name discards any fact about its fields and any location it had:
   they described whatever it held before. *)
let bind name t (d : t) : t =
  List.map
    (fun c ->
      let others = List.filter (fun (q, _) -> q.root <> name) c.bindings in
      { c with bindings = (var name, t) :: others; locs = List.remove_assoc name c.locs })
    d

(* Record which object a variable denotes. [None] leaves it unknown. *)
let set_loc name (l : loc option) (d : t) : t =
  List.map
    (fun c ->
      let rest = List.remove_assoc name c.locs in
      { c with locs = (match l with Some l -> (name, l) :: rest | None -> rest) })
    d

let loc_of name (d : t) =
  match d with
  | [] -> None
  | c :: rest ->
      let first = List.assoc_opt name c.locs in
      (* only trust it when every disjunct agrees *)
      if List.for_all (fun c -> List.assoc_opt name c.locs = first) rest then first
      else None

(* Could these two PATHS be the same location? Their field chains must be
   prefix-compatible and their roots may be the same object. *)
let may_alias_root a b (d : t) =
  a = b
  ||
  match (loc_of a d, loc_of b d) with
  | Some x, Some y -> x = y
  | _ -> true

let may_alias (p : path) (q : path) (d : t) =
  let rec compatible a b =
    match (a, b) with
    | [], _ | _, [] -> true
    | x :: xs, y :: ys -> x = y && compatible xs ys
  in
  compatible p.fields q.fields && may_alias_root p.root q.root d

let type_in_conjunct c (p : path) =
  let rec go current prefix = function
    | [] -> current
    | f :: rest -> (
        let prefix = prefix @ [ f ] in
        match List.assoc_opt { root = p.root; fields = prefix } c.bindings with
        | Some t -> go (Some t) prefix rest
        | None -> (
            match current with
            | None -> None
            | Some t -> go (Ty.project t f) prefix rest))
  in
  go (List.assoc_opt (var p.root) c.bindings) [] p.fields

let lookup_path (p : path) (d : t) =
  match d with
  | [] -> None
  | _ ->
      let types = List.map (fun c -> type_in_conjunct c p) d in
      if List.for_all Option.is_some types then
        Some (Ty.any_of (List.map Option.get types))
      else None

let lookup name d = lookup_path (var name) d
let mem name (d : t) = Option.is_some (lookup name d)

let narrow existing t =
  if Subty.subty existing t then existing
  else if Subty.subty t existing then t
  else
    (* simplify: (string | number) & !string => number *)
    let intersected = Ty.and_ existing t in
    let rec drop = function
      | Ty.Or (a, b) -> Ty.or_ (drop a) (drop b)
      | arm -> if Empty.is_empty (Ty.and_ arm t) then Ty.bot else arm
    in
    let dropped = drop existing in
    if Subty.equiv dropped intersected then dropped else intersected

(* Replace what is recorded about a path, rather than narrowing it. This is a
   STRONG update: it claims the path now holds exactly this, which only an
   owner may say. The caller must have established that nothing else observes
   the old value. *)
let assign_path (p : path) t (d : t) : t =
  prune
    (List.map
       (fun c -> { c with bindings = (p, t) :: List.remove_assoc p c.bindings })
       d)

let refine_path (p : path) t (d : t) : t =
  prune
    (List.map
       (fun c ->
         match type_in_conjunct c p with
         | None -> c
         | Some existing ->
             {
               c with
               bindings = (p, narrow existing t) :: List.remove_assoc p c.bindings;
             })
       d)

let refine name t d = refine_path (var name) t d

(* Narrow by the complement, as the else-branch of a type test does. *)
let refine_path_out p t d = refine_path p (Ty.not_ t) d
let refine_out name t d = refine name (Ty.not_ t) d

(* Discard every recorded fact that a write through [p] could invalidate. *)
let forget_aliases (p : path) (d : t) : t =
  if is_var p then d
  else
    let rec compatible a b =
      match (a, b) with
      | [], _ | _, [] -> true
      | x :: xs, y :: ys -> x = y && compatible xs ys
    in
    List.map
      (fun c ->
        {
          c with
          bindings =
            List.filter
              (fun (q, _) ->
                is_var q
                || not (compatible p.fields q.fields && may_alias_root p.root q.root d))
              c.bindings;
        })
      d

let forget_path (p : path) (d : t) : t =
  let under (q : path) =
    q.root = p.root
    && List.length q.fields >= List.length p.fields
    && List.filteri (fun i _ -> i < List.length p.fields) q.fields = p.fields
  in
  List.map
    (fun c -> { c with bindings = List.filter (fun (q, _) -> not (under q)) c.bindings })
    d

let forget_fields (d : t) : t =
  List.map
    (fun c -> { c with bindings = List.filter (fun (q, _) -> is_var q) c.bindings })
    d

(* --- printing ------------------------------------------------------------- *)

let rec show_heap = function
  | Emp -> "emp"
  | PointsTo (x, t) -> x ^ " |-> " ^ Ty.show t
  | Star (a, b) -> show_heap a ^ " * " ^ show_heap b

let show_conjunct c =
  let binds =
    List.map (fun (p, t) -> show_path p ^ ": " ^ Ty.show t) (List.rev c.bindings)
  in
  match (c.heap, binds) with
  | Emp, [] -> "emp"
  | Emp, bs -> String.concat ", " bs
  | h, [] -> show_heap h
  | h, bs -> show_heap h ^ " /\\ " ^ String.concat ", " bs

let show (d : t) =
  match d with
  | [] -> "false"
  | cs -> String.concat " \\/ " (List.map show_conjunct cs)
