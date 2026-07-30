open Config
open Witness_common

open Cil_datatype

let formula_str f =
  SL2C.convert f

let state_yaml s =
  List.map formula_str s
  |> List.map (fun s -> "(" ^ s ^ ")")
  |> String.concat " || "

let yaml_loc loc =
  let pos : Filepath.position = fst loc in
  `O [
    "file_name", `String (Filepath.to_string_abs pos.pos_path);
    "line",      `Float (Float.of_int pos.pos_lnum);
    (*"column",    `Float (Float.of_int pos.pos_cnum);*)
  ]

let yaml_location stmt =
  let pos = fst @@ Cil_datatype.Stmt.loc stmt in
  `O [
    "file_name", `String (Filepath.to_string_abs pos.pos_path);
    "line",      `Float (Float.of_int pos.pos_lnum);
    (*"column",    `Float (Float.of_int pos.pos_cnum);*)
  ]

let yaml_invariant stmt state =
  `O ["invariant", `O [
    "type",     `String "loop_invariant";
    "location", yaml_location stmt;
    "value",    `String (state_yaml state);
    "format",   `String "sl_c_expression";
  ]]


let mk_invariants (results : (Stmt.t, Formula.state) Hashtbl.t) =
  Hashtbl.to_seq results
  |> List.of_seq
  |> List.filter_map (fun (stmt, state) ->
      if Common.is_loop stmt then Some (yaml_invariant stmt state)
      else None
    )

(** TODO: This is a temporal solution for predicates.

type predicate = {
  name : string;
  params : (string * Typ.t) list;
  definition : Astral.SL.t;
}
*)

let yaml_params (name, typ) =
  `O [
    "name",     `String name;
    "type",     `String typ;
  ]

let mk_predicate pred =
  let open Types in
  `O ["predicate", `O [
    "location",  yaml_loc pred.origin_stmt;
    "name",      `String pred.name;
    "params",    `A (List.map yaml_params pred.params);
    "definition", `String pred.definition;
  ]]

let mk_predicates predicates = List.map mk_predicate predicates

let mk_witness results =
  let specification = "CHECK( init(main()), LTL(G valid-memsafety) )" in (* TODO: correct? *)

  let uuid = get_uuid () in
  let time = current_time () in
  let data_model = get_data_model () in
  let architecture = get_architecture () in
  let files = get_files_with_hashes () in

  let task_yaml = `O [
    "input_files",        `A (List.map (fun (path, _) -> `String path) files);
    "input_file_hashes",  `O (List.map (fun (path, hash) -> (path, `String hash)) files);
    "specification",      `String specification;
    "data_model",         `String data_model;
    "language",           `String "C";
  ]
  in

  (* TODO: do not hardcore name and version here *)
  let producer_yaml = `O [
    "name",     `String "SEAL";
    "version",  `String "0.1";
  ]
  in

  let metadata = `O [
    "format_version", `String "2.2";
    "uuid",           `String uuid;
    "creation_time",  `String time;
    "producer",       producer_yaml;
    "task",           task_yaml;
  ]
  in
  let predicates = Types.get_predicates () in
  let logic_declarations = `O [
    "entry_type", `String "logic_declarations";
    "content",    `A (mk_predicates predicates);
  ]
  in

  let invariant_set = `O [
    "entry_type", `String "invariant_set";
    "metadata", metadata;
    "content",  `A (mk_invariants results);
  ] in

  if List.is_empty predicates
  then `A [invariant_set]
  else `A [logic_declarations; invariant_set]

let write results path =
  let witness = mk_witness results in
  let channel = Out_channel.open_text path in
  match Yaml.to_string witness with
  | Ok yaml ->
    Out_channel.output_string channel yaml;
    close_out channel
  | Error (`Msg err) ->
    Common.fail "Internal error when generating witness: %s" err
