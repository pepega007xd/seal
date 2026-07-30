open Config
open Astral

let parse_file filename =
  let lexbuf, lexer = Clexer.init ~filename Clexer.initial in
  let cabs = Cparser.file lexer lexbuf in
  Clexer.finish ();
  cabs

let formula_to_c_exp str =
  let unescape str =
    if String.starts_with ~prefix:"\"" str
    then List.nth (String.split_on_char '"' str) 1
    else str
  in
  let str = unescape str in
  let str = BatString.nreplace ~str ~sub:"\\canAccess" ~by:"canAccess" in
  let str = BatString.nreplace ~str ~sub:"\\at" ~by:"at" in
  let str = BatString.nreplace ~str ~sub:"&*&" ~by:"&&" in
  str

let declare_body body =
  let body = formula_to_c_exp body in
  Format.asprintf "int main(){\n return %s;\n}\n" body

let create_c_file name types params body =
  let filename = Filename.temp_file "witness_expr__" ".c" in
  let oc = open_out filename in
  output_string oc @@ declare_body body;
  close_out oc;
  filename

let parse position types name params body =
  let filename = create_c_file types name params body in
  let tokens = List.map snd @@ parse_file filename in
  Cabs2Expr.get position body params tokens
