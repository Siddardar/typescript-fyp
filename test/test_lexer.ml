open Ts_hoare_logic

let failures = ref 0
let total = ref 0

(* Token stream for a source string, minus the trailing EOF. *)
let tokens_of src =
  Parse.tokenise (Lexing.from_string src)
  |> Array.to_list
  |> List.map (fun (l : Token.located) -> l.Token.token)
  |> List.filter (fun t -> t <> Token.EOF)

let show_list ts = "[" ^ String.concat "; " (List.map Token.show ts) ^ "]"

let check src expected =
  incr total;
  match tokens_of src with
  | actual when actual = expected -> ()
  | actual ->
      incr failures;
      Printf.printf "FAIL  %S\n      expected: %s\n      actual:   %s\n" src
        (show_list expected) (show_list actual)
  | exception Lexer.Error msg ->
      incr failures;
      Printf.printf "FAIL  %S\n      %s\n" src msg

let check_rejects src =
  incr total;
  match tokens_of src with
  | ts ->
      incr failures;
      Printf.printf "FAIL  %S should not lex, got %s\n" src (show_list ts)
  | exception Lexer.Error _ -> ()

(* --- keywords versus identifiers ---------------------------------------- *)

let () =
  check "type" [ Token.KW_TYPE ];
  check "typeof" [ Token.KW_TYPEOF ];
  (* a keyword with anything appended is an identifier, not a keyword *)
  check "types" [ Token.IDENT "types" ];
  check "typeX" [ Token.IDENT "typeX" ];
  check "iffy" [ Token.IDENT "iffy" ];
  check "_let" [ Token.IDENT "_let" ];
  check "function if else let const return"
    [ Token.KW_FUNCTION; Token.KW_IF; Token.KW_ELSE; Token.KW_LET;
      Token.KW_CONST; Token.KW_RETURN ]

(* --- literals ------------------------------------------------------------ *)

let () =
  check "42" [ Token.NUMBER 42. ];
  check "3.14" [ Token.NUMBER 3.14 ];
  check "0" [ Token.NUMBER 0. ];
  (* "42." is a number then a dot, not a malformed number *)
  check "42." [ Token.NUMBER 42.; Token.DOT ];
  check {|"hello"|} [ Token.STRING "hello" ];
  check {|""|} [ Token.STRING "" ];
  check {|"a\"b"|} [ Token.STRING "a\"b" ];
  check {|"a\\b"|} [ Token.STRING "a\\b" ];
  check {|"a\nb"|} [ Token.STRING "a\nb" ];
  check_rejects {|"unterminated|};
  check_rejects "\"across\nlines\""

(* --- operators: longest match wins --------------------------------------- *)

let () =
  check "=" [ Token.EQUALS ];
  check "===" [ Token.EQ_CHECK ];
  check "!==" [ Token.NEQ_CHECK ];
  (* no spaces needed to separate them *)
  check "a===b" [ Token.IDENT "a"; Token.EQ_CHECK; Token.IDENT "b" ];
  check "a=b" [ Token.IDENT "a"; Token.EQUALS; Token.IDENT "b" ];
  check "a.b.c"
    [ Token.IDENT "a"; Token.DOT; Token.IDENT "b"; Token.DOT; Token.IDENT "c" ];
  check "()" [ Token.LPAREN; Token.RPAREN ];
  check_rejects "!"

(* --- comments ------------------------------------------------------------ *)

let () =
  check "a // trailing\nb" [ Token.IDENT "a"; Token.IDENT "b" ];
  check "a /* inline */ b" [ Token.IDENT "a"; Token.IDENT "b" ];
  check "a /* over\ntwo lines */ b" [ Token.IDENT "a"; Token.IDENT "b" ];
  check "// whole line" [];
  check_rejects "a /* unterminated"

(* --- a real fragment ------------------------------------------------------ *)

let () =
  check "type Box = { v: string | number }"
    [ Token.KW_TYPE; Token.IDENT "Box"; Token.EQUALS; Token.LBRACE;
      Token.IDENT "v"; Token.COLON; Token.IDENT "string"; Token.BAR;
      Token.IDENT "number"; Token.RBRACE ];
  check "b.v = 42;"
    [ Token.IDENT "b"; Token.DOT; Token.IDENT "v"; Token.EQUALS;
      Token.NUMBER 42.; Token.SEMICOLON ];
  check {|typeof b.v === "string"|}
    [ Token.KW_TYPEOF; Token.IDENT "b"; Token.DOT; Token.IDENT "v";
      Token.EQ_CHECK; Token.STRING "string" ]

(* --- positions ----------------------------------------------------------- *)

let () =
  incr total;
  let locs = Parse.tokenise (Lexing.from_string "a\n  bb\n") in
  let at i = (locs.(i).Token.line, locs.(i).Token.col) in
  if at 0 <> (1, 1) || at 1 <> (2, 3) then (
    incr failures;
    let l, c = at 1 in
    Printf.printf "FAIL  positions: second token at line %d, col %d\n" l c)

let () =
  Printf.printf "%d/%d passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1
