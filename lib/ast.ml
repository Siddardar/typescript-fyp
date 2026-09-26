type ty =
  | TypeName of string
  | TypeLit of lit_ty  (* "circle", 42 — a singleton type *)
  | TypeUnion of ty * ty
  | TypeObject of object_ty

  and lit_ty = LitStr of string | LitNum of float
  and object_ty = { fields: field list }
  and field = { name: string; ty: ty }

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

(* A declaration is a kind of statement, as in TypeScript itself. *)
type stmt =
  | TypeAlias of { 
      name : string; 
      ty : ty 
    }
  | FunctionDecl of {
      name : string;
      params : param list;
      ret_type : ty option;
      body : stmt list;
    }
  | If of { 
      cond : expr; 
      then_ : stmt; 
      else_ : stmt option 
    }
  | VarDecl of { 
      kind : var_kind; 
      name : string; 
      ty : ty option; 
      value : expr 
    }
  | Return of expr option
  | Block of stmt list
  | ExprStmt of expr          (* f(x); is an expression but written as a statement *)

  and param = { name : string; ty : ty }
  and var_kind = Let | Const

type program = stmt list
  
let rec show_type = function
  | TypeName n -> n
  | TypeLit (LitStr s) -> Printf.sprintf "%S" s
  | TypeLit (LitNum n) -> Printf.sprintf "%g" n
  | TypeUnion (a, b) -> show_type a ^ " | " ^ show_type b
  | TypeObject obj -> 
      let show_field (field : field) = 
        field.name ^ ": " ^ show_type field.ty
      in
    match obj.fields with
    | [] -> "{}"
    | fs -> "{ " ^ String.concat "; " (List.map show_field fs) ^ " }"

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

let rec show_stmt level s =
  let pad = String.make (level * 2) ' ' in
  match s with
  | TypeAlias { name; ty } -> pad ^ "type " ^ name ^ " = " ^ show_type ty ^ ";"
  | ExprStmt e -> pad ^ show_expr e ^ ";"
  | Return None -> pad ^ "return;"
  | Return (Some e) -> pad ^ "return " ^ show_expr e ^ ";"
  | VarDecl { kind; name; ty; value } ->
      pad
      ^ (match kind with Let -> "let " | Const -> "const ")
      ^ name
      ^ (match ty with None -> "" | Some t -> ": " ^ show_type t)
      ^ " = " ^ show_expr value ^ ";"
  | Block body -> pad ^ show_body level body
  | If { cond; then_; else_ } ->
      pad ^ "if (" ^ show_expr cond ^ ") "
      ^ show_branch level then_
      ^ (match else_ with None -> "" | Some e -> " else " ^ show_branch level e)
  | FunctionDecl { name; params; ret_type; body } ->
      let show_param (p : param) = p.name ^ ": " ^ show_type p.ty in
      pad ^ "function " ^ name ^ "("
      ^ String.concat ", " (List.map show_param params)
      ^ ")"
      ^ (match ret_type with None -> "" | Some t -> ": " ^ show_type t)
      ^ " " ^ show_body level body

(* A brace-delimited body, opening on the current line. *)
and show_body level body =
  let pad = String.make (level * 2) ' ' in
  match body with
  | [] -> "{}"
  | ss -> "{\n" ^ String.concat "\n" (List.map (show_stmt (level + 1)) ss) ^ "\n" ^ pad ^ "}"

(* A branch of an if: a block opens inline, anything else goes on its own line. *)
and show_branch level s =
  match s with Block body -> show_body level body | _ -> "\n" ^ show_stmt (level + 1) s

let show_program stmts = String.concat "\n" (List.map (show_stmt 0) stmts)
