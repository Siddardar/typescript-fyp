(* Elaboration

   Surface types -> tagged rows

     { x: A, y: B }   ->   { %tag: "", x: A, y: B }
     [A, B]           ->   { %tag: "", 0: A, 1: B }_c
     Point(A, B)      ->   { %tag: tok(Point), 0: A, 1: B }_c ("_c" -> closed)

   TODO: tuple and constructor syntax. *)

exception Error of string

let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* reserved type names -> core types *)
let builtin = function
  | "string" -> Some Ty.string_
  | "number" -> Some Ty.number_
  | "boolean" -> Some Ty.boolean_
  | "unknown" -> Some Ty.top
  | "never" -> Some Ty.bot
  | _ -> None

(* (type alias, core type) *)
type env = (string * Ty.t) list

let empty_env : env = []

(* resolves a bare name: a builtin, then an alias, then a failure.

   NOTE: any is rejected rather than mapped to unknown 
   TODO: check if allow? and if so how? *)
let lookup (env : env) name =
  match builtin name with
  | Some t -> t
  | None -> (
      match List.assoc_opt name env with
      | Some t -> t
      | None ->
          if name = "any" then
            error
              "'any' is not supported: it denotes no set of values, so it has no \
               meaning under semantic subtyping"
          else error "unknown type %s" name)

(* translates surface AST to core types *)
let rec elab resolve (t : Ast.ty) : Ty.t =
  match t with
  | Ast.TypeName n -> resolve n
  | Ast.TypeLit (Ast.LitStr s) -> Ty.str s
  | Ast.TypeLit (Ast.LitNum n) -> Ty.num n
  | Ast.TypeLit (Ast.LitBool b) -> Ty.bool_ b
  | Ast.TypeUnion (a, b) -> Ty.or_ (elab resolve a) (elab resolve b)
  | Ast.TypeObject { fields } -> object_row (List.map (elab_field resolve) fields)

and elab_field resolve (f : Ast.field) = (f.name, elab resolve f.ty)

and object_row fields =
  let row = Ty.record fields in
  match row with
  | Ty.Row r when not (Row.well_keyed r) -> error "duplicate field in an object type"
  | _ -> row

let ty (env : env) t = elab (lookup env) t

(* ts allows for types to be used before declaration hence:
    - first collect type alias
    - then elaborate
    
    NOTE: cannot represent recursive types cause keep track of aliases
    TODO: predicate layer -> allows for this *)

let program (stmts : Ast.program) : env =
  let declared =
    List.filter_map
      (function Ast.TypeAlias { name; ty } -> Some (name, ty) | _ -> None)
      stmts
  in
  (* Reject duplicates up front: the later one would silently shadow. *)
  let rec check_unique = function
    | [] -> ()
    | (name, _) :: rest ->
        if List.mem_assoc name rest then error "type %s is declared more than once" name
        else check_unique rest
  in
  check_unique declared;

  let resolved = Hashtbl.create 16 in
  (* [visiting] is the chain of aliases currently being resolved, so a cycle is
     detected instead of looping. *)
  let rec resolve visiting name =
    if builtin name <> None || not (List.mem_assoc name declared) then
      lookup empty_env name
    else
      match Hashtbl.find_opt resolved name with
      | Some t -> t
      | None ->
          if List.mem name visiting then
            error "type %s is recursive, which needs the predicate layer" name
          else
            let t = elab (resolve (name :: visiting)) (List.assoc name declared) in
            Hashtbl.replace resolved name t;
            t
  in
  List.map (fun (name, _) -> (name, resolve [] name)) declared

(* --- function signatures --------------------------------------------------

   Term variables live in their own namespace: TypeScript lets a type and a
   value share a name, so [type Box = ...] and [function Box() {}] coexist. *)

type term_env = (string * Ty.t) list

let empty_term_env : term_env = []

(* A function declaration becomes an arrow type.

   TODO: void. It is neither unknown nor never, and needs an undefined value
   type the kernel does not have yet. *)
let signature (env : env) name (params : Ast.param list) ret_type =
  let rec check_unique = function
    | [] -> ()
    | (p : Ast.param) :: rest ->
        if List.exists (fun (q : Ast.param) -> q.name = p.name) rest then
          error "parameter %s of %s is declared more than once" p.name name
        else check_unique rest
  in
  check_unique params;
  let param_types = List.map (fun (p : Ast.param) -> ty env p.ty) params in
  let result = match ret_type with Some t -> ty env t | None -> Ty.top in
  Ty.arrow param_types result

(* Collect every top-level function signature. Nested declarations are the
   checker's business, since they are scoped to a body. *)
let signatures (env : env) (stmts : Ast.program) : term_env =
  let declared =
    List.filter_map
      (function
        | Ast.FunctionDecl { name; params; ret_type; _ } -> Some (name, params, ret_type)
        | _ -> None)
      stmts
  in
  let rec check_unique = function
    | [] -> ()
    | (name, _, _) :: rest ->
        if List.exists (fun (n, _, _) -> n = name) rest then
          error "function %s is declared more than once" name
        else check_unique rest
  in
  check_unique declared;
  List.map (fun (name, params, ret) -> (name, signature env name params ret)) declared

