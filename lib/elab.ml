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
  | "true" -> Some (Ty.bool_ true)
  | "false" -> Some (Ty.bool_ false)
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
