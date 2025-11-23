open Cil_types

(** This module implements and registers callbacks for showing data in Ivette *)

(** Prints the current state associated with a statement when hovered over *)
let print_state (fmt : Format.formatter) (loc : Printer_tag.localizable) : unit
    =
  let result =
    match loc with
    | Printer_tag.PStmtStart (_, stmt) ->
        Hashtbl.find_opt !Func_call.function_context.results stmt
    | _ -> None
  in
  Option.iter (Formula.pp_state fmt) result

let pp_shared =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
    Cil_printer.pp_field

(** Prints the detected list type for a structure *)
let print_type_heuristic (fmt : Format.formatter)
    (loc : Printer_tag.localizable) : unit =
  let get_struct_type (typ : typ) =
    match Ast_types.unroll_deep_node typ with
    | TPtr { tnode = TComp structure; _ } | TComp structure -> (
        match Types.get_struct_type structure with
        | Sll (next, shared) ->
            Format.asprintf "Singly linked list\n next: %a\n shared: %a"
              Cil_printer.pp_field next pp_shared shared
        | Dll (next, prev, shared) ->
            Format.asprintf
              "Doubly linked list\n next: %a\n prev: %a\nshared: %a"
              Cil_printer.pp_field next Cil_printer.pp_field prev pp_shared
              shared
        | Nl (top, next, shared) ->
            Format.asprintf "Nested list\n top: %a\n next: %a\n shared: %a"
              Cil_printer.pp_field top Cil_printer.pp_field next pp_shared
              shared
        | Struct shared ->
            Format.asprintf "Struct\n shared: %a" pp_shared shared)
    | _ -> Format.asprintf "Non-structure type: %a" Printer.pp_typ typ
  in
  let result =
    match loc with
    | Printer_tag.PType typ -> Some (get_struct_type typ)
    | Printer_tag.PVDecl (_, _, var) -> Some (get_struct_type var.vtype)
    | _ -> None
  in
  Option.iter (Format.pp_print_string fmt) result

(** Prints the detected field type for a field of a structure *)
let print_type_heuristic_on_field (fmt : Format.formatter)
    (loc : Printer_tag.localizable) : unit =
  let result =
    match loc with
    | Printer_tag.PLval (_, _, (_, Field (field, _))) -> (
        match Types.get_field_type field with
        | Next -> Some "next"
        | Prev -> Some "prev"
        | Top -> Some "top"
        | Other field -> Some ("other: " ^ field))
    | _ -> None
  in
  Option.iter (Format.pp_print_string fmt) result

let () =
  Server.Kernel_ast.Information.register ~id:"seal.stmt_state" ~label:"state"
    ~title:"final state" ~descr:"final state reached for this statement"
    print_state;

  Server.Kernel_ast.Information.register ~id:"seal.type_heuristic"
    ~label:"type heurisic" ~title:"type heuristic"
    ~descr:"result of type heurisitic (which list type is this?)"
    print_type_heuristic;

  Server.Kernel_ast.Information.register ~id:"seal.field_type_heuristic"
    ~label:"field type heurisic" ~title:"field type heuristic"
    ~descr:"result of field type heurisitic (which list field type is this?)"
    print_type_heuristic_on_field
