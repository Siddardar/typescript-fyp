open Ts_hoare_logic

let usage () =
  prerr_endline "usage: main parse <file>";
  prerr_endline "       main parse-string <text>";
  exit 1

let run show f arg =
  match f arg with
  | ast -> print_endline (show ast)
  | exception Parser.Syntax_error msg ->
      prerr_endline ("error: " ^ msg);
      exit 1

let () =
  match Array.to_list Sys.argv with
    | _ :: "parse" :: path :: _ -> run Ast.show_program Parser.of_file path
    | _ :: "parse-string" :: text :: _ ->
      run Ast.show_program Parser.of_string text
  | _ -> usage ()
