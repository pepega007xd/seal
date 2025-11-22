open Cil
open Cil_types
open Astral
open Constants
open Common

(** This module implements the analysis of C types that determines, which list
    types they represent *)

(** Classification of structs *)
type struct_type =
  (* next, others *)
  | Sll of fieldinfo * fieldinfo list
  (* next, prev, others *)
  | Dll of fieldinfo * fieldinfo * fieldinfo list
  (* top, next, others *)
  | Nl of fieldinfo * fieldinfo * fieldinfo list
  | Struct of fieldinfo list

(** Classification of struct fields *)
type field_type = Next | Prev | Top | Other of string | Data

let pp_typ_node fmt tnode = Cil_printer.pp_typ fmt { tnode; tattr = [] }

let is_relevant_type (typ : typ) : bool =
  match Ast_types.unroll_deep_node typ with
  | TComp _ | TPtr _ -> true
  | _ -> false

let is_relevant_var (var : varinfo) = is_relevant_type var.vtype

let get_struct_pointer_fields (structure : compinfo) : fieldinfo list =
  structure.cfields |> Option.get
  |> List.filter (fun field -> is_relevant_type field.ftype)

let rec get_self_and_sll_fields (structure : compinfo) :
    fieldinfo list * fieldinfo list * fieldinfo list =
  let self_fields, other =
    structure |> get_struct_pointer_fields
    |> List.partition (fun field ->
        match Ast_types.unroll_deep_node field.ftype with
        | TPtr { tnode = TComp target_struct; _ } ->
            target_struct.ckey = structure.ckey
        | _ -> false)
  in
  let sll_fields, other_fields =
    List.partition
      (fun field ->
        match Ast_types.unroll_deep_node field.ftype with
        | TPtr { tnode = TComp structure; _ } -> (
            match get_struct_type structure with Sll _ -> true | _ -> false)
        | _ -> false)
      other
  in
  (self_fields, sll_fields, other_fields)

(** Determines, which list type a structure represents based on its fields *)
and get_struct_type (structure : compinfo) : struct_type =
  let self_fields, sll_fields, other_fields =
    get_self_and_sll_fields structure
  in

  match (self_fields, sll_fields) with
  | [ next ], [] -> Sll (next, other_fields)
  | [ top ], [ next ] -> Nl (top, next, other_fields)
  | [ next; prev ], [] -> Dll (next, prev, other_fields)
  | _ -> Struct (self_fields @ sll_fields @ other_fields)

(** Determines the type of field in the context of lists *)
let get_field_type (field : fieldinfo) : field_type =
  let self_fields, sll_fields, _ = get_self_and_sll_fields field.fcomp in

  match (self_fields, sll_fields) with
  (* SLL *)
  | [ next ], [] when field.forder = next.forder -> Next
  (* DLL *)
  | [ next; _ ], [] when field.forder = next.forder -> Next
  | [ _; prev ], [] when field.forder = prev.forder -> Prev
  (* NL *)
  | [ top ], [ _ ] when field.forder = top.forder -> Top
  | [ _ ], [ next ] when field.forder = next.forder -> Next
  | _ -> if is_relevant_type field.ftype then Other field.fname else Data

let type_info : (typ_node, Sort.t * MemoryModel.StructDef.t) Hashtbl.t =
  Hashtbl.create 113

let rec get_type_info (typ : typ) : Sort.t * MemoryModel.StructDef.t =
  let typ = Ast_types.unroll_deep_node typ in
  Hashtbl.find_opt type_info typ |> function
  | Some result -> result
  | None ->
      let dummy_struct_def = MemoryModel.StructDef.mk "dummy_struct_def" [] in
      let result =
        match typ with
        | TPtr { tnode = TComp structure; _ } -> (
            let name = structure.cname in
            let sort = Sort.mk_loc name in

            let create_struct self_fields other_fields =
              let self_fields =
                List.map
                  (fun field -> MemoryModel.Field.mk field.fname sort)
                  self_fields
              in
              let other_fields =
                List.map
                  (fun field ->
                    let sort = field.ftype |> get_type_info |> fst in
                    MemoryModel.Field.mk field.fname sort)
                  other_fields
              in
              ( MemoryModel.StructDef.mk name (self_fields @ other_fields),
                other_fields )
            in

            match get_struct_type structure with
            | Sll (next, shared) ->
                let struct_def, shared = create_struct [ next ] shared in
                List_constructors.register_ls name sort struct_def shared
            | Dll (next, prev, shared) ->
                let struct_def, shared = create_struct [ next; prev ] shared in
                List_constructors.register_dls name sort struct_def shared
            | Nl (top, next, shared) ->
                let struct_def, shared =
                  create_struct [ top ] (next :: shared)
                in
                List_constructors.register_nls name sort struct_def shared
            | Struct shared ->
                let struct_def, _ = create_struct [] shared in
                (sort, struct_def))
        | TPtr { tnode = TInt _; _ } ->
            let name = "intptr" in
            let sort = Sort.mk_loc name in
            let struct_def = MemoryModel.StructDef.mk name [] in
            (sort, struct_def)
        | TPtr inner ->
            let name = Common.get_unique_name "ptr2ptr" in
            let sort = Sort.mk_loc name in
            let inner_sort = get_type_info inner |> fst in
            let field =
              MemoryModel.Field.mk Constants.ptr_field_name inner_sort
            in
            let struct_def = MemoryModel.StructDef.mk name [ field ] in
            (sort, struct_def)
        | _ -> (Sort.loc_nil, dummy_struct_def)
      in
      if snd result <> dummy_struct_def then Hashtbl.add type_info typ result;
      result

let get_struct_def (sort : Sort.t) : MemoryModel.StructDef.t =
  Hashtbl.to_seq_values type_info
  |> Seq.find (fun (s, _) -> sort = s)
  |> Option.get |> snd

let get_list_type (sort : Sort.t) : struct_type =
  Hashtbl.to_seq type_info
  |> Seq.find_map (function
    | TPtr { tnode = TComp structure; _ }, (s, _) when s = sort ->
        Some (get_struct_type structure)
    | _ -> None)
  |> Option.get

let get_next_sort_of_nls (nls_sort : Sort.t) =
  let struct_def = get_struct_def nls_sort in
  match MemoryModel.StructDef.get_fields struct_def with
  | _ :: next :: _ -> MemoryModel0.Field.get_sort next
  | _ -> assert false

(** Converts the type of a variable into its sort, and creates an SL variable *)
let varinfo_to_var (varinfo : Cil_types.varinfo) : SL.Variable.t =
  let name = "v_" ^ varinfo.vname in
  match () with
  | _ when Ast_types.is_integral varinfo.vtype ->
      SL.Variable.mk name (Sort.mk_bitvector 32)
  | _ when not @@ is_relevant_var varinfo ->
      fail "invalid type in varinfo_to_var: %a" Printer.pp_varinfo varinfo
  | _ ->
      let sort = varinfo.vtype |> get_type_info |> fst in
      SL.Variable.mk name sort

(** Memoizes list types inside [get_type_info] *)
let process_types =
  object
    inherit Visitor.frama_c_inplace

    method! vtype (typ : typ) =
      if is_relevant_type typ then ignore @@ get_type_info typ;
      SkipChildren
  end

(** Generates struct definitions for generic structs and sets them in the solver*)
let process_types (file : file) =
  Visitor.visitFramacFileFunctions process_types file;

  let heap_sort =
    Hashtbl.to_seq_values type_info |> List.of_seq |> HeapSort.of_list
  in
  Common.solver :=
    Some (Solver.add_heap_sort heap_sort (Option.get !Common.solver))
