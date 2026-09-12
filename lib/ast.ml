type ty =
  | TypeName of string
  | TypeUnion of ty * ty
  | TypeObject of object_ty

and object_ty = { fields: field list }
and field = { name: string; ty: ty }

type declaration = TypeAlias of { name : string; ty : ty}

type program = declaration list
  
let rec show_type = function
  | TypeName n -> n
  | TypeUnion (a, b) -> show_type a ^ " | " ^ show_type b
  | TypeObject obj -> 
      let show_field field = 
        field.name ^ ": " ^ show_type field.ty
      in
    match obj.fields with
    | [] -> "{}"
    | fs -> "{ " ^ String.concat "; " (List.map show_field fs) ^ " }"

let show_decleration = function
  | TypeAlias { name; ty } -> 
      "type " ^ name ^ " = " ^ show_type ty ^ ";"

let show_program declarations = String.concat "\n" (List.map show_decleration declarations)
