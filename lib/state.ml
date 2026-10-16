(* --- heap assertions ------------------------------------------------------
   who owns what memory
   Unused while the checker is flow-insensitive *)

type heap =
  | Emp  (* no cell is owned *)
  | PointsTo of string * Ty.t  (* x |-> t: owned exclusively, holding a t *)
  | Star of heap * heap

(* --- states ---------------------------------------------------------------
   TODO: existential quantification. Paper A writes each conjunct as
   exists v*. sigma /\ pi; fresh result variables will need it at entailment. *)

type conjunct = { heap : heap; bindings : (string * Ty.t) list }

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
      { c with bindings = (name, t) :: List.remove_assoc name c.bindings })
    d

let lookup name (d : t) =
  match d with
  | [] -> None
  | _ ->
      let types = List.map (fun c -> List.assoc_opt name c.bindings) d in
      if List.for_all Option.is_some types then
        Some (Ty.any_of (List.map Option.get types))
      else None

let mem name (d : t) = Option.is_some (lookup name d)

let narrow existing t =
  if Subty.subty existing t then existing
  else if Subty.subty t existing then t
  else Ty.and_ existing t

let refine name t (d : t) : t =
  prune
    (List.map
       (fun c ->
         match List.assoc_opt name c.bindings with
         | None -> c
         | Some existing ->
             { c with bindings = (name, narrow existing t) :: List.remove_assoc name c.bindings })
       d)

let refine_out name t d = refine name (Ty.not_ t) d

(* --- printing ------------------------------------------------------------- *)

let rec show_heap = function
  | Emp -> "emp"
  | PointsTo (x, t) -> x ^ " |-> " ^ Ty.show t
  | Star (a, b) -> show_heap a ^ " * " ^ show_heap b

let show_conjunct c =
  let binds =
    List.map (fun (x, t) -> x ^ ": " ^ Ty.show t) (List.rev c.bindings)
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
