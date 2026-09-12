exception Error of string

type state = { 
  tokens: Token.located array; 
  mutable pos : int;
}

let make tokens = { tokens; pos = 0 }

let current_token_located state = state.tokens.(state.pos)
let peek_token state = (current_token_located state).Token.token

let peek_token_at state n = 
  let i = min (state.pos + n) (Array.length state.tokens - 1) in (* EOF alw last token*)
  state.tokens.(i).Token.token

let advance_pos state = 
  if state.pos < Array.length state.tokens - 1
    then state.pos <- state.pos + 1

let failure_msg state expected = 
  let tok_located = current_token_located state in
  raise
    (Error
      (Printf.sprintf "line %d, col %d: expected %s, found %s"
        tok_located.Token.line 
        tok_located.Token.col
        expected 
        (Token.show tok_located.Token.token)))

let expect_token state token expected =
  if peek_token state = token 
    then advance_pos state
  else failure_msg state expected  

let expect_ident state = 
  match peek_token state with 
  | Token.IDENT name ->
      advance_pos state;
      name
  | _ -> failure_msg state "an identifier"
