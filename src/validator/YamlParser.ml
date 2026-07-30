(** Yaml witness format parser. *)

open Astral

open Cil_datatype

open CorrectnessWitness

let fail msg =
  Format.printf "%s" msg;
  exit 1

let get_string = function
  | `String str -> str
  | _ -> fail "expecting string"

let find ?default key yaml_object =
  match Yaml.Util.find key yaml_object, default with
  | Ok (Some res), _ -> res
  | Ok None, Some default -> default
  | Ok None, None -> fail @@ Format.asprintf "Key '%s' is missing in:\n %s" key (Yaml.to_string_exn yaml_object)
  | Error (`Msg msg), _ -> fail msg

let find_string ?default key yaml_object =
  let default = Option.map (fun b -> `String b) default in
  match find ?default key yaml_object with
  | `String str -> str
  | _ -> fail "expecting string"

let find_int key yaml_object =
  match find key yaml_object with
  | `Float f when Float.is_integer f -> Float.to_int f
  | _ -> fail "expecting int"

let find_bool ?default key yaml_object =
  let default = Option.map (fun b -> `Bool b) default in
  match find ?default key yaml_object with
  | `Bool b -> b
  | _ -> fail "expecting bool"

let find_list ?(empty_default=false) elem_fn key yaml_object =
  let default = if empty_default then Some (`A []) else None in
  match find ?default key yaml_object with
  | `A xs -> List.map elem_fn xs
  | _ -> fail "expecting bool"

let is_entry_type entry_type yaml_object =
  match Yaml.Util.find "entry_type" yaml_object with
  | Ok (Some `String str) -> String.equal str entry_type
  | _ -> false

let find_entry ?default entry_type entries =
  try List.find (is_entry_type entry_type) entries
  with Not_found ->
    match default with
    | None -> failwith ("No entry with type: " ^ entry_type)
    | Some default -> default


(** High-level get functions *)

let get_location yaml =
  find "location" yaml
  |> find_int "line"

(** *)

let sort_of_c_type str =
  let open Logic_typing in
  (* TODO: what to do with typedefs? *)
  let name = String.split_on_char ' ' str |> List.hd in
  let ctype = Globals.Types.find_type Struct name in
  Types.sort_of_type @@ Cil_const.mk_tptr ctype

let parse_definition = ()


(** *)

let find_struct name =
  let name = List.nth (String.split_on_char ' ' name) 0 in
  try Globals.Types.find_type Logic_typing.Struct name
  with _ -> failwith ("No structure: " ^ name)


let get_types params =
  List.filter_map (function `O [_, _; "type", `String typ] -> Some typ | _ -> None) params
  |> List.sort_uniq String.compare
  |> List.map find_struct

let parse_param = function
  | `O ["name", `String name; "type", `String typ] ->
    let sort = sort_of_c_type typ in
    SL.Variable.mk name sort
  | _ -> failwith "TODO"

let parse_params = function
  | `A ps ->
    let params = List.map parse_param ps in
    let types = get_types ps in
    types, params
  | _ -> failwith "TODO"

let parse_definition params body =
  ExprParser.parse params body

let parse_predicate = function
  | `O ["predicate", decl] ->
    let name = find_string "name" decl in
    let types, params = parse_params @@ find "params" decl in
    let definition = parse_definition 0 (* TODO! *) name types params @@ find_string "definition" decl in
    InductiveDefinition.mk name params definition
  | `O _ -> failwith "TODO"
  | _ -> failwith "Expecting object in declaration"

let parse_predicates = function
  | `A decls -> List.map parse_predicate decls
  | _ -> failwith "Expecting list of declarations in `content`"

let parse_logic_declarations yaml = match yaml with
  | `O _ ->
    let content = Option.get @@ Yaml.Util.find_exn "content" yaml in
    parse_predicates content

  | _ -> failwith "Expecting object `logic_declarations`"

(** {2 Parsing of invariants} *)

let parse_invariant = function
  | `O [_, invariant] ->
    let line = get_location invariant in
    let value = find_string "value" invariant in
    let labels = find_list ~empty_default:true (get_string) "labels" invariant in
    let invariant = Invariant.{
      location = line;
      raw_content = value;
      should_be_inductive = List.mem "inductive" labels;
      content = ExprParser.parse line "invariant" [] [] value;
    }
    in
    (line, invariant)
  | _ -> assert false

let parse_invariants = function
  | `A invariants ->
    List.map parse_invariant invariants
    |> InvariantMap.of_list
  | _ -> failwith "Expecting object list of invariants"

let parse_invariant_set yaml = match yaml with
  | `O _ ->
    let content = Option.get @@ Yaml.Util.find_exn "content" yaml in
    parse_invariants content
  | _ -> failwith "Expecting object `logic_declarations`"

let parse_yaml = function
  | `A entries ->
    let predicates = find_entry ~default:(`O ["content", `A []]) "logic_declarations" entries in
    let invariants = find_entry ~default:(`O []) "invariant_set" entries in
    {
      predicates = parse_logic_declarations predicates;
      invariants = parse_invariant_set invariants
    }
  | _ -> failwith "Toplevel error"

let parse path =
  let module IC = In_channel in
  let text = IC.with_open_text path IC.input_all in
  match Yaml.of_string text with
    | Ok yaml -> parse_yaml yaml
    | Error (`Msg msg) -> failwith msg
