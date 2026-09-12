open Ts_hoare_logic

let usage () =
  prerr_endline "usage: main parse <file>";
  prerr_endline "       main parse-string <text>";
  prerr_endline "       main parse-type <text>";
  exit 1

let run show f arg =
  match f arg with
  | ast -> print_endline (show ast)
  | exception Parse.Syntax_error msg ->
      prerr_endline ("error: " ^ msg);
      exit 1

let () =
  match Array.to_list Sys.argv with
  | _ :: "parse" :: path :: _ -> run Ast.show_program (Parse.of_file Parser.program_entry) path
  | _ :: "parse-string" :: text :: _ ->
      run Ast.show_program (Parse.of_string Parser.program_entry) text
  | _ :: "parse-type" :: text :: _ ->
      run Ast.show_type (Parse.of_string TypeParser.ty_entry) text
  | _ -> usage ()
