open Astral

(** This module implements the transfer function for most of the basic
    instructions defined in [Instruction_type] *)

(** transfer function for [var = var;] *)
let assign (lhs : Formula.var) (rhs : Formula.var) (formula : Formula.t) :
    Formula.t =
  formula |> Formula.substitute_by_fresh lhs |> Formula.add_eq lhs rhs

(** transfer function for [var->field = var;] *)
let assign_lhs_field (lhs : Formula.var) (lhs_field : Types.field_type)
    (rhs : Formula.var) (formula : Formula.t) : Formula.t =
  Formula.change_pto_target lhs lhs_field rhs formula

(** transfer function for [*var = var;] *)
let assign_lhs_deref (lhs : Formula.var) (rhs : Formula.var)
    (formula : Formula.t) : Formula.t =
  Formula.get_ref_opt lhs formula |> function
  | Some lhs_target ->
      (* stack pointer *)
      assign lhs_target rhs formula |> Formula.update_ref lhs lhs_target
  | None ->
      Formula.change_pto_target lhs (Other Constants.int_field_name) rhs formula

(** transfer function for function calls *)
let call (lhs_sort : SL.Sort.t) (func : Cil_types.varinfo)
    (args : Formula.var list) (formula : Formula.t) :
    Formula.t list * Formula.var list =
  let get_allocation (init_vars_to_null : bool) =
    let lhs = SL.Variable.mk_fresh "call_ret" lhs_sort in
    let pto =
      let fields =
        Types.get_struct_def lhs_sort |> MemoryModel.StructDef.get_fields
      in
      let names = List.map MemoryModel.Field.show fields in
      let vars =
        (* TODO: initialize int fields to zero, not nil *)
        if init_vars_to_null then List.map (fun _ -> Formula.nil) fields
        else
          List.map MemoryModel.Field.get_sort fields
          |> List.map (SL.Variable.mk_fresh (SL.Variable.get_name lhs))
      in
      let fields = List.combine names vars in

      match (Types.get_list_type lhs_sort, fields) with
      | Sll _, next :: shared -> Formula.PointsTo (lhs, LS_t (snd next), shared)
      | Dll _, prev :: next :: shared ->
          Formula.PointsTo (lhs, DLS_t (snd prev, snd next), shared)
      | Nl _, top :: next :: shared ->
          Formula.PointsTo (lhs, NLS_t (snd top, snd next), shared)
      | _ -> Formula.PointsTo (lhs, Generic, fields)
    in

    let allocation = formula |> Formula.add_atom pto in
    if Options.Svcomp_mode.get () then ([ allocation ], [ lhs ])
    else
      ( [
          (* success *)
          allocation;
          (* failure *)
          formula
          |> Formula.substitute_by_fresh lhs
          |> Formula.add_eq lhs Formula.nil;
        ],
        [ lhs; lhs ] )
  in

  match (func.vname, args) with
  | "malloc", _ -> get_allocation false
  | "calloc", _ -> get_allocation true
  (*TODO: *)
  (* | "realloc", var :: _ -> *)
  (*     (* realloc changes the pointer value => all references to `var` are now dangling *) *)
  (*     Formula.materialize var formula *)
  (*     |> List.map (fun formula -> *)
  (*            let spatial_atom = Formula.get_spatial_atom_from var formula in *)
  (*            formula *)
  (*            |> Formula.remove_spatial_from var *)
  (*            |> Formula.substitute_by_fresh var *)
  (*            |> Formula.add_atom spatial_atom) *)
  | "free", [ src ] -> (
      try
        formula |> Formula.materialize src
        |> List.map (Formula.remove_spatial_from src)
        |> List.map (Formula.add_atom @@ Formula.Freed src)
        |> List.map (fun f -> (f, Formula.nil))
        |> List.split
      with
      | Formula.Bug (Invalid_deref (var, formula), pos) ->
          raise @@ Formula.Bug (Invalid_free (var, formula), pos)
      | e -> raise e)
  | "__VERIFIER_nondet_int", _ -> ([ formula ], [ Formula.nondet ])
  | _, args -> Func_call.func_call args func formula lhs_sort
