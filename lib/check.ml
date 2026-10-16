exception Type_error of string

let error fmt = Printf.ksprintf (fun s -> raise (Type_error s)) fmt

type ctx = { types : Elab.env; result : Ty.t option }

(* --- projecting a field out of a type ------------------------------------ *)
let rec project t label =
  match t with
  | Ty.Row r -> Row.lookup label r
  | Ty.Or (a, b) -> (
      match (project a label, project b label) with
      | Some x, Some y -> Some (Ty.or_ x y)
      | _ -> None  (* absent from one arm: not readable from the whole *)
      )
  | Ty.And (a, b) -> (
      match (project a label, project b label) with
      | Some x, Some y -> Some (Ty.and_ x y)
      | Some x, None | None, Some x -> Some x
      | None, None -> None)
  | _ -> None

let as_arrow = function Ty.Arrow (ps, r) -> Some (ps, r) | _ -> None

let rec typeof_tags t =
  let merge a b = List.sort_uniq compare (a @ b) in
  let every = [ "string"; "number"; "boolean"; "object"; "function" ] in
  match t with
  | Ty.Base Ty.String | Ty.Lit (Ty.LStr _) -> [ "string" ]
  | Ty.Base Ty.Number | Ty.Lit (Ty.LNum _) -> [ "number" ]
  | Ty.Base Ty.Boolean | Ty.Lit (Ty.LBool _) -> [ "boolean" ]
  | Ty.Row _ -> [ "object" ]
  | Ty.Arrow _ -> [ "function" ]
  | Ty.Or (a, b) -> merge (typeof_tags a) (typeof_tags b)
  | Ty.And (a, b) ->
      List.filter (fun s -> List.mem s (typeof_tags b)) (typeof_tags a)
  | Ty.Bot -> []
  | Ty.Top | Ty.Not _ -> every

(* --- expressions ---------------------------------------------------------- *)
let rec synth ctx d (e : Ast.expr) : Ty.t =
  match e with
  | Ast.Ident x -> (
      match State.lookup x d with
      | Some t -> t
      | None -> error "%s is not defined" x)
  | Ast.Number n -> Ty.num n
  | Ast.String s -> Ty.str s
  | Ast.ObjectLit props ->
      Ty.record (List.map (fun (p : Ast.prop) -> (p.name, synth ctx d p.value)) props)
  | Ast.Member (obj, field) -> (
      let t = synth ctx d obj in
      match project t (Row.Name field) with
      | Some ft -> ft
      | None -> error "property %s does not exist on type %s" field (Ty.show t))
  | Ast.Call (callee, args) -> (
      let ft = synth ctx d callee in
      match as_arrow ft with
      | None -> error "%s is not callable: its type is %s" (Ast.show_expr callee) (Ty.show ft)
      | Some (params, result) ->
          let got = List.length args and want = List.length params in
          if got <> want then
            error "%s expects %d argument%s but got %d" (Ast.show_expr callee) want
              (if want = 1 then "" else "s")
              got
          else (
            List.iter2 (fun a p -> check ctx d a p) args params;
            result))
  | Ast.Assign (lhs, rhs) ->
      let target = assign_target ctx d lhs in
      check ctx d rhs target;
      synth ctx d rhs
  | Ast.Unary (Ast.TypeOf, operand) ->
      let t = synth ctx d operand in
      Ty.any_of (List.map Ty.str (typeof_tags t))
  | Ast.Binary (_, a, b) ->
      ignore (synth ctx d a);
      ignore (synth ctx d b);
      Ty.boolean_

and assign_target ctx d (lhs : Ast.expr) =
  match lhs with
  | Ast.Ident x -> (
      match State.lookup x d with
      | Some t -> t
      | None -> error "%s is not defined" x)
  | Ast.Member (obj, field) -> (
      let t = synth ctx d obj in
      match project t (Row.Name field) with
      | Some ft -> ft
      | None -> error "property %s does not exist on type %s" field (Ty.show t))
  | _ -> error "%s is not assignable" (Ast.show_expr lhs)

(* Verify a term against a type already known *)
and check ctx d (e : Ast.expr) (expected : Ty.t) =
  let actual = synth ctx d e in
  if not (Subty.subty actual expected) then
    error "%s has type %s, which is not assignable to %s" (Ast.show_expr e)
      (Ty.show actual) (Ty.show expected)

(* --- statements -----------------------------------------------------------
   takes a state and returns a state *)

let rec stmt ctx d (s : Ast.stmt) : State.t =
  match s with
  | Ast.TypeAlias _ -> d  (* already resolved into the type environment *)
  | Ast.ExprStmt e ->
      ignore (synth ctx d e);
      d
  | Ast.VarDecl { name; ty = annotation; value; _ } ->
      let t =
        match annotation with
        | Some a ->
            let declared = Elab.ty ctx.types a in
            check ctx d value declared;
            declared
        | None -> synth ctx d value
      in
      State.bind name t d
  | Ast.Return e -> (
      match (ctx.result, e) with
      | None, _ -> error "return outside a function"
      | Some expected, Some value ->
          check ctx d value expected;
          d
      | Some expected, None ->
          if not (Subty.subty Ty.top expected) then
            error "this function must return %s" (Ty.show expected);
          d)
  | Ast.Block body ->
      (* Bindings made inside a block do not escape it. *)
      ignore (block ctx d body);
      d
  | Ast.If { cond; then_; else_ } ->
      ignore (synth ctx d cond);
      ignore (stmt ctx d then_);
      (match else_ with None -> () | Some s -> ignore (stmt ctx d s));
      d
  | Ast.FunctionDecl _ -> d  (* bodies are checked by [program] *)

and block ctx d body = List.fold_left (fun d s -> stmt ctx d s) d body

let prelude =
  [ ("console", Ty.record [ ("log", Ty.arrow [ Ty.top ] Ty.top) ]) ]

let program (prog : Ast.program) =
  let types = Elab.program prog in
  let signatures = Elab.signatures types prog in

  let top =
    List.fold_left
      (fun d (name, t) -> State.bind name t d)
      State.init (prelude @ signatures)
  in
  let check_decl d (s : Ast.stmt) =
    match s with
    | Ast.FunctionDecl { name; params; body; _ } ->
        let result =
          match List.assoc_opt name signatures with
          | Some (Ty.Arrow (_, r)) -> Some r
          | _ -> None
        in
        let inner =
          List.fold_left
            (fun d (p : Ast.param) -> State.bind p.name (Elab.ty types p.ty) d)
            d params
        in
        ignore (block { types; result } inner body);
        d
    | s -> stmt { types; result = None } d s
  in
  ignore (List.fold_left check_decl top prog)

let run (prog : Ast.program) =
  match program prog with
  | () -> Ok ()
  | exception Type_error msg -> Error msg
  | exception Elab.Error msg -> Error msg
