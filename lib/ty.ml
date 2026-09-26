(* The type language

   A type denotes a set of values. The connectives are genuine union,
   intersection and complement, and subtyping is set inclusion. Because
   complement is available, one emptiness test decides subtyping, pattern
   exhaustiveness, arm reachability, flow refinement and inhabitation alike *)

type t =
  | Top  (* every value -> approx ts's unknown *)
  | Bot  (* no value; ts's never *)
  | Base of base
  | Lit of lit  (* a singleton: the one-element set containing this value *)
  | Row of t Row.t
  | And of t * t
  | Or of t * t
  | Not of t

and base = String | Number | Boolean
and lit = LStr of string | LNum of float | LBool of bool

(* Every literal -> exactly one base type *)
let base_of_lit = function
  | LStr _ -> String
  | LNum _ -> Number
  | LBool _ -> Boolean

(* smart constructors -> simplify then build nodes *)
let top = Top
let bot = Bot
let string_ = Base String
let number_ = Base Number
let boolean_ = Base Boolean
let str s = Lit (LStr s)
let num n = Lit (LNum n)
let bool_ b = Lit (LBool b)

let rec not_ = function
  | Top -> Bot
  | Bot -> Top
  | Not a -> a  (* double negation *)
  | And (a, b) -> Or (not_ a, not_ b)  (* De Morgan, pushing negation inward *)
  | Or (a, b) -> And (not_ a, not_ b)
  | a -> Not a

let and_ a b =
  match (a, b) with
  | Bot, _ | _, Bot -> Bot
  | Top, x | x, Top -> x
  | x, y when x = y -> x
  (* complement: a & !a is empty *)
  | x, Not y when x = y -> Bot
  | Not x, y when x = y -> Bot
  | _ -> And (a, b)

let or_ a b =
  match (a, b) with
  | Top, _ | _, Top -> Top
  | Bot, x | x, Bot -> x
  | x, y when x = y -> x
  (* complement: a | !a is everything *)
  | x, Not y when x = y -> Top
  | Not x, y when x = y -> Top
  | _ -> Or (a, b)

(* A \ B, subtyping -> empty? *)
let diff a b = and_ a (not_ b)

let any_of ts = List.fold_left or_ bot ts
let all_of ts = List.fold_left and_ top ts

(* row constructor shortcuts *)
let row r = Row r
let record fields = Row (Row.record fields)
let tuple items = Row (Row.tuple items)
let unit_ = Row Row.unit_row
let constr name items = Row (Row.constr name items)
let constr_record name fields = Row (Row.constr_record name fields)
let constr_named name fields = Row (Row.constr_named name fields)

(* printing: ts spelling *)
let show_base = function String -> "string" | Number -> "number" | Boolean -> "boolean"

let show_lit = function
  | LStr s -> Printf.sprintf "%S" s
  | LNum n -> Printf.sprintf "%g" n
  | LBool b -> if b then "true" else "false"

let rec show t = show_or t

and show_or = function
  | Or (a, b) -> show_or a ^ " | " ^ show_or b
  | t -> show_and t

and show_and = function
  | And (a, b) -> show_and a ^ " & " ^ show_and b
  | t -> show_not t

and show_not = function Not a -> "!" ^ show_atom a | t -> show_atom t

and show_atom = function
  | Top -> "unknown"
  | Bot -> "never"
  | Base b -> show_base b
  | Lit l -> show_lit l
  | Row r -> Row.show show r
  | (And _ | Or _ | Not _) as t -> "(" ^ show t ^ ")"
