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

type conjunct = { heap : heap; bindings : (path * Ty.t) list }

(* A disjunction. The empty list is false: no state satisfies it, so the
   program point is unreachable. *)
type t = conjunct list

let unreachable : t = []
let is_unreachable (d : t) = d = []
let init : t = [ { heap = Emp; bindings = [] } ]
let conjuncts (d : t) = d

let prune (d : t) =
  List.filter (fun c -> not (List.exists (fun (_, t) -> Empty.is_empty t) c.bindings)) d

let or_ (a : t) (b : t) : t = a @ b

(* --- bindings ------------------------------------------------------------- *)

let bind name t (d : t) : t =
  List.map
    (fun c ->
      let others = List.filter (fun (q, _) -> q.root <> name) c.bindings in
      { c with bindings = (var name, t) :: others })
    d

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
              (fun (q, _) -> is_var q || not (compatible p.fields q.fields))
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
