(* Tagged rows

   records, tuples and constructors have a finite map from labels to values, plus one
   %tag slot with the only diff in:
   - the token in the %tag slot
   - whether the remaining labels are named, numeric, or composite. *)

type token =
  | Anon  (* "" empty tag *)
  | Tok of string  (* tok(C) — unqiue to one declaration *)

(* Open {} -> "at least these fields" -> records
   Closed () -> exactly this arity (num of args) -> tuple. *)
type kind = Open | Closed

type label =
  | Name of string  (* f: from a open declaration *)
  | Pos of int  (* i: an unnamed positional field, 0-based *)
  | Composite of string * int  (* f@i — a named positional field *)

type 'a t = { tag : token; kind : kind; fields : (label * 'a) list }

(* check if field can satisfy demand -> label matching *)
let answers field demand =
  match (field, demand) with
  | Name f, Name g -> f = g
  | Pos i, Pos j -> i = j
  | Composite (f, i), Composite (g, j) -> f = g && i = j
  | Composite (f, _), Name g -> f = g
  | Composite (_, i), Pos j -> i = j
  | _ -> false

let name_of = function Name f | Composite (f, _) -> Some f | Pos _ -> None
let pos_of = function Pos i | Composite (_, i) -> Some i | Name _ -> None

(* The field whose label answers [demand], if any. *)
let lookup demand row =
  List.find_map (fun (l, v) -> if answers l demand then Some v else None) row.fields

let mem demand row = Option.is_some (lookup demand row)

(* checks if fields are duplicates -> more than one field cannot meet a demand *)
let no_duplicates xs =
  let sorted = List.sort compare xs in
  let rec check = function
    | a :: (b :: _ as rest) -> a <> b && check rest
    | _ -> true
  in
  check sorted

let well_keyed row =
  no_duplicates (List.filter_map (fun (l, _) -> name_of l) row.fields)
  && no_duplicates (List.filter_map (fun (l, _) -> pos_of l) row.fields)

(* records, tuples, etc -> tagged row *)
let make ~tag ~kind ~fields = { tag; kind; fields }

(* { x: a, y: b } — anonymous, named, open *)
let record fields = { tag = Anon; kind = Open; fields = List.map (fun (n, v) -> (Name n, v)) fields }

(* (a, b) — anonymous, numeric, closed *)
let tuple items = { tag = Anon; kind = Closed; fields = List.mapi (fun i v -> (Pos i, v)) items }

(* () — the empty closed row *)
let unit_row = { tag = Anon; kind = Closed; fields = [] }

(* C(a, b) — from data C(A, B) *)
let constr name items =
  { tag = Tok name; kind = Closed; fields = List.mapi (fun i v -> (Pos i, v)) items }

(* C{x: a} — from data C{x: A} *)
let constr_record name fields =
  { tag = Tok name; kind = Open; fields = List.map (fun (n, v) -> (Name n, v)) fields }

(* C(x: a, y: b) — from data C(x: A, y: B), the named-positional form, whose
   fields answer both spellings *)
let constr_named name fields =
  {
    tag = Tok name;
    kind = Closed;
    fields = List.mapi (fun i (n, v) -> (Composite (n, i), v)) fields;
  }

let map f row = { row with fields = List.map (fun (l, v) -> (l, f v)) row.fields }

(*  printing -> closed row is marked with _c. *)

let show_token = function Anon -> {|""|} | Tok c -> "tok(" ^ c ^ ")"

let show_label = function
  | Name f -> f
  | Pos i -> string_of_int i
  | Composite (f, i) -> f ^ "@" ^ string_of_int i

let show show_value row =
  let field (l, v) = show_label l ^ ": " ^ show_value v in
  let parts = ("%tag: " ^ show_token row.tag) :: List.map field row.fields in
  "{ " ^ String.concat ", " parts ^ " }" ^ match row.kind with Closed -> "_c" | Open -> ""
