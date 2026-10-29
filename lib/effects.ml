(* What a function writes. 
   reads each body and records the writes in terms of the
   function's own parameters *)

(* A write, named from inside the function: parameter [param], then [fields]. *)
(* [wrote] is the type left behind, when that is known AND the write always
   happens. A write inside a branch may not have run, so claiming the new type
   would be wrong; such a write records None and the caller falls back to the
   declared type. *)
type target = { param : int; fields : string list; wrote : Ty.t option }

type t =
  | Writes of target list
  | Unknown  (* anything reachable may have been written *)

type env = (string * t) list

let callee_name (e : Ast.expr) =
  match e with
  | Ast.Ident f -> Some f
  | Ast.Member (Ast.Ident o, m) -> Some (o ^ "." ^ m)
  | _ -> None

(* The prelude writes nothing. *)
let initial : env = [ ("console.log", Writes []) ]

(* A recursive call can append a field on every pass:

     function f(b) { b.v = 1; f(b.next); }

   gives $0.v, then $0.next.v, then $0.next.next.v, without end. Bounding the
   chain and truncating to the prefix keeps the fixpoint finite. Truncating is
   sound because invalidating a prefix discards everything beneath it, so the
   real write is still covered.

   This is k-limiting, the usual answer in points-to and shape analysis. The
   bound is a PRECISION knob, not a correctness one: a chain deeper than this
   is widened to its prefix, so the checker invalidates more than it has to
   and rejects programs it could have accepted. It never accepts one it
   should not.

   Detecting a cycle in the call graph does not replace it. Both of

     function ping(b) { pong(b); }  function pong(b) { b.v = 1; ping(b); }
     function f(b)    { b.v = 1; f(b.next); }

   are cycles; the first settles in three passes and the second never does.
   What separates them is whether going round the cycle EXTENDS a parameter
   path. Detecting that exactly means computing the strongly connected
   components of the call graph and composing the argument substitutions
   around each cycle, since the growth can be spread across several functions:

     function a(b) { c(b.next); }   function c(b) { b.v = 1; a(b); }

   Neither of those extends anything on its own. That refinement is worth
   doing, and is worth doing after ownership: no program the checker currently
   accepts can reach the bound, because growth of this kind needs a recursive
   type and Elab rejects those. *)
let max_depth = 4

(* Truncating loses track of which location was written, so the type written
   there no longer describes the path that remains. *)
let truncate (t : target) =
  if List.length t.fields <= max_depth then t
  else { t with fields = List.filteri (fun i _ -> i < max_depth) t.fields; wrote = None }

(* Two writes to the same path agree on the type only if they wrote the same
   thing; otherwise the caller learns nothing about it. *)
let merge (x : target list) (y : target list) =
  List.fold_left
    (fun acc (t : target) ->
      match
        List.partition (fun (s : target) -> s.param = t.param && s.fields = t.fields) acc
      with
      | [], _ -> t :: acc
      | (s : target) :: _, rest ->
          let wrote = if s.wrote = t.wrote then s.wrote else None in
          { t with wrote } :: rest)
    x y

let union a b =
  match (a, b) with
  | Unknown, _ | _, Unknown -> Unknown
  | Writes x, Writes y -> Writes (merge x y)

(* The type a write leaves behind, when it can be read off the expression
   without type checking. Anything else is unknown. *)
let wrote_type (e : Ast.expr) =
  match e with
  | Ast.Number n -> Some (Ty.num n)
  | Ast.String s -> Some (Ty.str s)
  | Ast.Bool b -> Some (Ty.bool_ b)
  | _ -> None

let is_fresh (e : Ast.expr) =
  match e with
  | Ast.ObjectLit _ | Ast.Number _ | Ast.String _ | Ast.Bool _ -> true
  | _ -> false

let of_body (env : env) (params : Ast.param list) (body : Ast.stmt list) =
  let index name =
    let rec go i = function
      | [] -> None
      | (p : Ast.param) :: rest -> if p.name = name then Some i else go (i + 1) rest
    in
    go 0 params
  in
  let acc = ref (Writes []) in
  let record t = acc := union !acc (Writes [ truncate t ]) in
  let unknown () = acc := Unknown in

  let rec resolve locals (e : Ast.expr) : target option =
    match e with
    | Ast.Ident x -> (
        match index x with
        | Some i -> Some { param = i; fields = []; wrote = None }
        | None -> List.assoc_opt x locals)
    | Ast.Member (obj, f) ->
        Option.map (fun t -> { t with fields = t.fields @ [ f ] }) (resolve locals obj)
    | _ -> None
  in

  (* [cond] is true inside a branch, where a write may not run. *)
  let rec expr cond locals (e : Ast.expr) =
    match e with
    | Ast.Assign (lhs, rhs) -> (
        expr cond locals rhs;
        match resolve locals lhs with
        | Some t -> record { t with wrote = (if cond then None else wrote_type rhs) }
        | None -> ())
    | Ast.Call (callee, args) -> (
        List.iter (expr cond locals) args;
        match Option.bind (callee_name callee) (fun n -> List.assoc_opt n env) with
        | None -> unknown ()  (* not a name we know: assume the worst *)
        | Some Unknown -> unknown ()
        | Some (Writes targets) ->
            List.iter
              (fun (t : target) ->
                match List.nth_opt args t.param with
                | None -> unknown ()
                | Some arg -> (
                    match resolve locals arg with
                    | Some base ->
                        record
                          {
                            base with
                            fields = base.fields @ t.fields;
                            wrote = (if cond then None else t.wrote);
                          }
                    | None -> if not (is_fresh arg) then unknown ()))
              targets)
    | Ast.Member (obj, _) -> expr cond locals obj
    | Ast.Unary (_, a) -> expr cond locals a
    | Ast.Binary (_, a, b) ->
        expr cond locals a;
        expr cond locals b
    | Ast.ObjectLit props ->
        List.iter (fun (p : Ast.prop) -> expr cond locals p.value) props
    | Ast.Ident _ | Ast.Number _ | Ast.String _ | Ast.Bool _ -> ()
  in

  let rec stmt cond locals (s : Ast.stmt) =
    match s with
    | Ast.TypeAlias _ -> locals
    | Ast.ExprStmt e ->
        expr cond locals e;
        locals
    | Ast.VarDecl { name; value; _ } ->
        expr cond locals value;
        (* a local bound to a parameter path becomes an alias for it *)
        (match resolve locals value with
        | Some t -> (name, t) :: List.remove_assoc name locals
        | None -> List.remove_assoc name locals)
    | Ast.Return (Some e) ->
        expr cond locals e;
        locals
    | Ast.Return None -> locals
    | Ast.Block body ->
        ignore (List.fold_left (stmt cond) locals body);
        locals
    | Ast.If { cond = guard; then_; else_ } ->
        expr cond locals guard;
        (* a write inside either branch may not run *)
        ignore (stmt true locals then_);
        (match else_ with None -> () | Some s -> ignore (stmt true locals s));
        locals
    (* TODO: captured variables e.g. inner fn that takes outer fn params
      function outer(b: Box) {
        function inner(): number { b.v = 42; return 1; }
      }
      cause inner has no params and currently it expresses write targets by param index
       => (* [wrote] is the type left behind, when that is known AND the write always
   happens. A write inside a branch may not have run, so claiming the new type
   would be wrong; such a write records None and the caller falls back to the
   declared type. *)
type target = { param : int; fields : string list; wrote : Ty.t option }
    *)
    | Ast.FunctionDecl _ -> locals
  in
  ignore (List.fold_left (stmt false) [] body);
  !acc

let analyse (prog : Ast.program) : env =
  let functions =
    List.filter_map
      (function
        | Ast.FunctionDecl { name; params; body; _ } -> Some (name, params, body)
        | _ -> None)
      prog
  in
  let env = ref (initial @ List.map (fun (n, _, _) -> (n, Writes [])) functions) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (name, params, body) ->
        let computed = of_body !env params body in
        if List.assoc_opt name !env <> Some computed then (
          changed := true;
          env := (name, computed) :: List.remove_assoc name !env))
      functions
  done;
  !env

let show = function
  | Unknown -> "unknown"
  | Writes [] -> "nothing"
  | Writes ts ->
      String.concat ", "
        (List.map
           (fun t ->
             String.concat "." (Printf.sprintf "$%d" t.param :: t.fields)
             ^ match t.wrote with None -> "" | Some ty -> " := " ^ Ty.show ty)
           ts)
