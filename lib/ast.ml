type ty =
  | TypeName of string
  | TypeUnion of ty * ty
  | TypeObject of object_ty

  and object_ty = { fields: field list }
  and field = { name: string; ty: ty }

type declaration = TypeAlias of { name : string; ty : ty}

type expr = 
  | Ident of string
  | Number of float
  | String of string
  | Member of expr * string       (* a.v *)
  | Call of expr * expr list      (* f(x, y) *)
  | Unary of unop * expr          (* typeof a *)
  | Binary of binop * expr * expr (* a === b *)
  | Assign of expr * expr         (* a = 1 OR a.v = 1 *)
  | ObjectLit of prop list        (* f({v: "a"}) *)

  and unop = TypeOf
  and binop = StrictEq | StrictNeq
  and prop = { name: string; value: expr }

type program = declaration list
  
let rec show_type = function
  | TypeName n -> n
  | TypeUnion (a, b) -> show_type a ^ " | " ^ show_type b
  | TypeObject obj -> 
      let show_field (field : field) = 
        field.name ^ ": " ^ show_type field.ty
      in
    match obj.fields with
    | [] -> "{}"
    | fs -> "{ " ^ String.concat "; " (List.map show_field fs) ^ " }"

let show_declaration = function
  | TypeAlias { name; ty } -> 
      "type " ^ name ^ " = " ^ show_type ty ^ ";"

let rec show_expr = function
  | Ident n -> n
  | Number n -> Printf.sprintf "%g" n
  | String s -> Printf.sprintf "%S" s
  | Member (expr, name) -> show_expr expr ^ "." ^ name
  | Call (func, args) ->
      show_expr func ^ "(" ^ String.concat ", " (List.map show_expr args) ^ ")"
  | Unary (TypeOf, expr) -> "(typeof " ^ show_expr expr ^ ")"
  | Binary (binop, a, b) ->
      let op_str =
        match binop with StrictEq -> " === " | StrictNeq -> " !== "
      in
      "(" ^ show_expr a ^ op_str ^ show_expr b ^ ")"
  | Assign (lhs, rhs) -> "(" ^ show_expr lhs ^ " = " ^ show_expr rhs ^ ")"
  | ObjectLit props ->
      let show_prop (prop : prop) = 
        prop.name ^ ": " ^ show_expr prop.value
      in
      
      match props with 
      | [] -> "{}"
      | p -> "{ " ^ String.concat ", " (List.map show_prop p) ^ " }"

let show_program declarations = String.concat "\n" (List.map show_declaration declarations)
