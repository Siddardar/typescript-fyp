open Ts_hoare_logic

let usage () =
  prerr_endline "usage: main check <file>        type-check a program";
  prerr_endline "       main check-string <text>";
  prerr_endline "       main parse <file>        print the parsed AST";
  prerr_endline "       main parse-string <text>";
  exit 1

let parse show f arg =
  match f arg with
  | ast -> print_endline (show ast)
  | exception Parser.Syntax_error msg ->
      prerr_endline ("syntax error: " ^ msg);
      exit 1

let check f arg =
  match f arg with
  | ast -> (
      match Check.run ast with
      | Ok () -> print_endline "ok"
      | Error msg ->
          prerr_endline ("type error: " ^ msg);
          exit 1)
  | exception Parser.Syntax_error msg ->
      prerr_endline ("syntax error: " ^ msg);
      exit 1

let () =
  match Array.to_list Sys.argv with
  | _ :: "check" :: path :: _ -> check Parser.of_file path
  | _ :: "check-string" :: text :: _ -> check Parser.of_string text
  | _ :: "parse" :: path :: _ -> parse Ast.show_program Parser.of_file path
  | _ :: "parse-string" :: text :: _ -> parse Ast.show_program Parser.of_string text
  | _ -> usage ()
