exception Type_error of string

let error fmt = Printf.ksprintf (fun s -> raise (Type_error s)) fmt

type ctx = { types : Elab.env; result : Ty.t option; effects : Effects.env }

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

type refinement = (State.path * Ty.t) list

let rec path_of (e : Ast.expr) : State.path option =
  match e with
  | Ast.Ident x -> Some (State.var x)
  | Ast.Member (obj, f) -> Option.map (fun p -> State.field p f) (path_of obj)
  | _ -> None

(* inverse of [typeof_tags *)
let type_of_tag = function
  | "string" -> Some Ty.string_
  | "number" -> Some Ty.number_
  | "boolean" -> Some Ty.boolean_
  | _ -> None

(* narrowing survives call? => handled by the Call rule. *)
let rec narrows (e : Ast.expr) : refinement * refinement =
  let none = ([], []) in
  match e with
  (* typeof <path> === "string", in either operand order *)
  | Ast.Binary (op, Ast.Unary (Ast.TypeOf, subject), Ast.String tag)
  | Ast.Binary (op, Ast.String tag, Ast.Unary (Ast.TypeOf, subject)) -> (
      match (path_of subject, type_of_tag tag, op) with
      | Some p, Some t, Ast.StrictEq -> ([ (p, t) ], [ (p, Ty.not_ t) ])
      | Some p, Some t, Ast.StrictNeq -> ([ (p, Ty.not_ t) ], [ (p, t) ])
      | _ -> none)
  (* Negation swaps the two branches. *)
  | Ast.Unary (Ast.Not, inner) ->
      let when_true, when_false = narrows inner in
      (when_false, when_true)
  (* Both halves of an && hold when it holds. When it fails, either could have,
     so nothing is known. || is the mirror. *)
  | Ast.Binary (Ast.And, a, b) ->
      let ta, _ = narrows a and tb, _ = narrows b in
      (ta @ tb, [])
  | Ast.Binary (Ast.Or, a, b) ->
      let _, fa = narrows a and _, fb = narrows b in
      ([], fa @ fb)
  | _ -> none

let apply (r : refinement) d =
  List.fold_left (fun d (p, t) -> State.refine_path p t d) d r

(* --- expressions ----------------------------------------------------------
   a call may write any field *)
let rec synth ctx d (e : Ast.expr) : Ty.t * State.t =
  match e with
  | Ast.Ident x -> (
      match State.lookup x d with
      | Some t -> (t, d)
      | None -> error "%s is not defined" x)
  | Ast.Number n -> (Ty.num n, d)
  | Ast.String s -> (Ty.str s, d)
  | Ast.Bool b -> (Ty.bool_ b, d)
  | Ast.ObjectLit props ->
      let fields, d =
        List.fold_left
          (fun (acc, d) (p : Ast.prop) ->
            let t, d = synth ctx d p.value in
            ((p.name, t) :: acc, d))
          ([], d) props
      in
      (Ty.record (List.rev fields), d)
  | Ast.Member (obj, field) -> (
      (* check the state first *)
      match Option.bind (path_of e) (fun p -> State.lookup_path p d) with
      | Some t -> (t, d)
      | None -> (
          let t, d = synth ctx d obj in
          match Ty.project t field with
          | Some ft -> (ft, d)
          | None -> error "property %s does not exist on type %s" field (Ty.show t)))
  | Ast.Call (callee, args) -> (
      let ft, d = synth ctx d callee in
      match as_arrow ft with
      | None -> error "%s is not callable: its type is %s" (Ast.show_expr callee) (Ty.show ft)
      | Some (params, result) ->
          let got = List.length args and want = List.length params in
          if got <> want then
            error "%s expects %d argument%s but got %d" (Ast.show_expr callee) want
              (if want = 1 then "" else "s")
              got
          else
            (* args evaluated first *)
            let d = List.fold_left2 (fun d a p -> check ctx d a p) d args params in
            (result, apply_effects ctx d callee args))
  | Ast.Assign (lhs, rhs) ->
      let target, d = assign_target ctx d lhs in
      let t, d = synth ctx d rhs in
      if not (Subty.subty t target) then
        error "%s has type %s, which is not assignable to %s" (Ast.show_expr rhs)
          (Ty.show t) (Ty.show target);
      (* write invalidates target and anything that could be the same mem location
         TODO: needs ownership *)
      let d =
        match path_of lhs with
        | Some p -> State.forget_aliases p (State.forget_path p d)
        | None -> State.forget_fields d
      in
      (t, d)
  | Ast.Unary (Ast.TypeOf, operand) ->
      let t, d = synth ctx d operand in
      (Ty.any_of (List.map Ty.str (typeof_tags t)), d)
  | Ast.Unary (Ast.Not, operand) ->
      let _, d = synth ctx d operand in
      (Ty.boolean_, d)
  | Ast.Binary (op, a, b) ->
      let ta, d = synth ctx d a in
      let tb, d = synth ctx d b in
      let t =
        match op with
        (* && and || evaluate to one of their operands, not to a boolean *)
        | Ast.And | Ast.Or -> Ty.or_ ta tb
        | Ast.StrictEq | Ast.StrictNeq -> Ty.boolean_
      in
      (t, d)

(* invalidate what a call writes*)
and apply_effects ctx d callee args =
  match
    Option.bind (Effects.callee_name callee) (fun n -> List.assoc_opt n ctx.effects)
  with
  | None | Some Effects.Unknown -> State.forget_fields d
  | Some (Effects.Writes targets) ->
      List.fold_left
        (fun d (t : Effects.target) ->
          match List.nth_opt args t.param with
          | None -> State.forget_fields d
          | Some arg -> (
              match path_of arg with
              | None -> d
              | Some base ->
                  let written = List.fold_left State.field base t.fields in
                  State.forget_aliases written (State.forget_path written d)))
        d targets

and assign_target ctx d (lhs : Ast.expr) =
  match lhs with
  | Ast.Ident x -> (
      match State.lookup x d with
      | Some t -> (t, d)
      | None -> error "%s is not defined" x)
  | Ast.Member (obj, field) -> (
      let t, d = synth ctx d obj in
      match Ty.project t field with
      | Some ft -> (ft, d)
      | None -> error "property %s does not exist on type %s" field (Ty.show t))
  (* Unreachable from parsed source: the parser rejects a non-lvalue here. *)
  | _ -> error "%s is not assignable" (Ast.show_expr lhs)

(* Verify a term against a type already known, and return the state after it. *)
and check ctx d (e : Ast.expr) (expected : Ty.t) : State.t =
  let actual, d = synth ctx d e in
  if not (Subty.subty actual expected) then
    error "%s has type %s, which is not assignable to %s" (Ast.show_expr e)
      (Ty.show actual) (Ty.show expected);
  d

(* --- statements -----------------------------------------------------------
   takes a state and returns a state *)

let rec stmt ctx d (s : Ast.stmt) : State.t =
  match s with
  | Ast.TypeAlias _ -> d  (* already resolved into the type environment *)
  | Ast.ExprStmt e ->
      let _, d = synth ctx d e in
      d
  | Ast.VarDecl { name; ty = annotation; value; _ } ->
      let t, d =
        match annotation with
        | Some a ->
            let declared = Elab.ty ctx.types a in
            (declared, check ctx d value declared)
        | None -> synth ctx d value
      in
      State.bind name t d
  | Ast.Return e -> (
      match (ctx.result, e) with
      | None, _ -> error "return outside a function"
      | Some expected, Some value -> check ctx d value expected
      | Some expected, None ->
          if not (Subty.subty Ty.top expected) then
            error "this function must return %s" (Ty.show expected);
          d)
  | Ast.Block body ->
      (* Bindings made inside a block do not escape it. *)
      ignore (block ctx d body);
      d
  | Ast.If { cond; then_; else_ } ->
      (* condition evaluated first *)
      let _, d = synth ctx d cond in
      let when_true, when_false = narrows cond in
      let d_then = apply when_true d and d_else = apply when_false d in
      let after_then =
        if State.is_unreachable d_then then d_then else stmt ctx d_then then_
      in
      let after_else =
        match else_ with
        | None -> d_else
        | Some s -> if State.is_unreachable d_else then d_else else stmt ctx d_else s
      in
      (* TODO: after [if (typeof x === "string") { return; }] this still
         believes x is string | number. *)
      State.or_ after_then after_else
  | Ast.FunctionDecl { name; params; ret_type; body } ->
      (* nested declaration is checked here *)
      let signature = Elab.signature ctx.types name params ret_type in
      let d = State.bind name signature d in
      check_body ctx d name params ret_type body;
      d

and block ctx d body = List.fold_left (fun d s -> stmt ctx d s) d body

and always_returns (s : Ast.stmt) =
  match s with
  | Ast.Return _ -> true
  | Ast.Block body -> List.exists always_returns body
  | Ast.If { then_; else_ = Some e; _ } -> always_returns then_ && always_returns e
  | _ -> false

and check_body ctx d name (params : Ast.param list) ret_type body =
  let result =
    match ret_type with Some a -> Elab.ty ctx.types a | None -> Ty.top
  in
  let inner =
    List.fold_left
      (fun d (p : Ast.param) -> State.bind p.name (Elab.ty ctx.types p.ty) d)
      d params
  in
  ignore (block { ctx with result = Some result } inner body);
  if ret_type <> None && not (List.exists always_returns body) then
    error "%s must return %s on every path" name (Ty.show result)

let prelude =
  [ ("console", Ty.record [ ("log", Ty.arrow [ Ty.top ] Ty.top) ]) ]

let program (prog : Ast.program) =
  let types = Elab.program prog in
  let signatures = Elab.signatures types prog in
  let effects = Effects.analyse prog in

  let top =
    List.fold_left
      (fun d (name, t) -> State.bind name t d)
      State.init (prelude @ signatures)
  in
  let check_decl d (s : Ast.stmt) =
    match s with
    | Ast.FunctionDecl { name; params; ret_type; body } ->
        check_body { types; result = None; effects } d name params ret_type body;
        d
    | s -> stmt { types; result = None; effects } d s
  in
  ignore (List.fold_left check_decl top prog)

let run (prog : Ast.program) =
  match program prog with
  | () -> Ok ()
  | exception Type_error msg -> Error msg
  | exception Elab.Error msg -> Error msg
