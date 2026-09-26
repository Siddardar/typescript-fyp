exception Parse_error of string

type state = { tokens: Token.located array; pos: int}
type error = { at: int; expected: string list }
type 'a parser_t = state -> ('a * state, error) result

(* helpers *)
let make tokens = { tokens; pos = 0 }
let located st = st.tokens.(st.pos)
let peek st = (located st).Token.token
let fail_at st what = Error { at = st.pos; expected = [ what ] }

(* monads: return, bind, map, keep right, keep left *)
let return x = fun st -> Ok(x, st) (* alw succeeds *)

(* parse smth then use f(v) to create a parser to parse the next token *)
let bind parser func = 
  fun st -> 
    match parser st with 
    | Ok (value, st') -> func value st'
    | Error e -> Error e

let ( let* ) = bind

(* parse smth then use f to change its value *)
let map parser func = 
  fun st -> 
    match parser st with 
    | Ok (value, st') -> Ok(func value, st')
    | Error e -> Error e

let ( >>| ) parser func = map parser func

(* discard value from left parser *)
let ( *> ) parser_left parser_right = 
  let* _ = parser_left in 
  parser_right

(* discard value from right parser *)
let ( <* ) parser_left parser_right = 
  let* value = parser_left in
  let* _ = parser_right in
  return value

(* try two different parsers. 
   if first advanced before failing throw error 
   else keep state for second parser

   if both fail keep error of further one *)
let alt parser_p parser_q =
  fun st -> 
    match parser_p st with
    | Ok _ as ok -> ok
    | Error e1 when e1.at > st.pos -> Error e1
    | Error e1 -> (
        match parser_q st with
        | Ok _ as ok -> ok
        | Error e2 when e2.at > e1.at -> Error e2
        | Error e2 when e2.at < e1.at -> Error e1
        | Error e2 -> Error { e2 with expected = e1.expected @ e2.expected }
    )
let ( <|> ) = alt

(* Makes a failure look non-consuming, so alt and many backtrack past it.
   Needed wherever a partial match is legitimately not an error, such as the
   trailing separator in a list. *)
let attempt parser =
  fun st -> 
    match parser st with 
    | Error e -> Error { e with at = st.pos } 
    | ok -> ok

(* try multiple parsers. stop at first succesful parser *)
let choice parsers = 
  match parsers with
  | [] -> fun st -> fail_at st "nothing"
  | p :: ps -> List.fold_left ( <|> ) p ps

(* expect smth when parsing *)
let label parser expected = 
  fun st -> 
    match parser st with 
    (* A committed failure has a real, specific error. Only relabel a parser
       that failed before consuming anything. *)
    | Error e when e.at > st.pos -> Error e
    | Error e -> Error { e with expected = [ expected ]}
    | ok -> ok

let ( <?> ) parser expected = label parser expected

(* primitives *)
let eof = 
  fun st ->
    if peek st = Token.EOF then 
      Ok ((), st)
    else
      fail_at st "end of input"

(* Always fails, consuming nothing. Lets a let* chain reject on a condition
   the grammar cannot express, such as an invalid assignment target. *)
let fail expected = fun st -> fail_at st expected

let satisfy expected func = 
  fun st -> 
    match func (peek st) with 
    | Some value -> Ok(value, { st with pos = st.pos + 1})
    | None -> fail_at st expected

let token tok =
  satisfy (Token.show tok) (fun t -> if t = tok then Some () else None)

let ident = satisfy "an identifier" (function Token.IDENT n -> Some n | _ -> None)
let number = satisfy "a number" (function Token.NUMBER n -> Some n | _ -> None)
let str_lit = satisfy "a string" (function Token.STRING s -> Some s | _ -> None)

(* run parser 0 or more times *)
let many parser = 
  let rec go acc st = 
    match parser st with 
    (* A failure that consumed input is committed: the element was clearly
       intended, so report its error rather than quietly ending the list. *)
    | Error e when e.at > st.pos -> Error e
    | Error _ -> Ok(List.rev acc, st)
    | Ok (x, st') when st'.pos > st.pos -> go (x :: acc) st'
    | Ok (x, st') -> Ok (List.rev (x :: acc), st')
  in
  go[]

(* runs parser 1 or more times *)
let many1 parser = 
  let* x = parser in
  let* xs = many parser in
  return (x :: xs)

let opt p = alt (p >>| Option.some) (return None)
let sep_by1 sep p = let* x = p in let* xs = many (sep *> p) in return ( x :: xs)
let sep_by sep p = alt (sep_by1 sep p) (return [])
let between l r p = l *> p <* r

(* Like sep_by, but a trailing separator is allowed. Note the trailing opt is
   inside the non-empty branch: otherwise an empty list would consume nothing
   and the opt would accept a LEADING separator. *)
let sep_by_trailing sep p =
  alt
    (let* x = p in
     let* xs = many (attempt (sep *> p)) in
     let* _ = opt sep in
     return (x :: xs))
    (return [])

(* left fold with op while parsing *)
let chainl1 parser op = 
  let rec go acc = alt (let* func = op in let* rhs = parser in go (func acc rhs)) (return acc) in
  let* first = parser in
  go first

(* running *)
let run parser tokens = 
  match (parser <* eof) (make tokens) with 
  | Ok (x, _) -> Ok x
  | Error e -> 
      let l = tokens.(e.at) in
      let expected = String.concat " or " (List.sort_uniq compare e.expected) in
      Error
        (Printf.sprintf "line %d, col %d: expected %s, found %s" 
          l.Token.line
          l.Token.col
          expected
          (Token.show l.Token.token)
        )
    