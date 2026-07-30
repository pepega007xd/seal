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
      (* regular pointer to integer *)
      Formula.assert_allocated lhs formula;
      formula

(** Materialization *)

(** transforms [formula] so that [var] is a part of a points-to atom, not a list
    segment, multiple formulas can be produced, representing different lengths
    of [ls] (1, 2+) *)
let rec materialize (var : Formula.var) (f : Formula.t) : Formula.t list =
  let open Formula in
  let open Common in
  let fresh_var = mk_fresh_var_from var in
  let f = make_var_explicit_src var f in
  let old_atom = get_spatial_atom_from var f in
  let f = f |> remove_atom old_atom in

  match old_atom with
  | PointsTo _ -> [ add_atom old_atom f ]
  (* ls has minimum length greater than zero -> just decrement and split off PointsTo *)
  | LS ls when ls.min_len > 0 ->
      [
        f
        |> add_atom (PointsTo (var, LS_t fresh_var))
        |> add_atom @@ mk_ls fresh_var ls.next (ls.min_len - 1);
      ]
  (* ls has minimum length equal to zero -> case split to 0 and 1+ *)
  | LS ls ->
      (* case where ls has length 1+ *)
      (f
      |> add_atom (PointsTo (var, LS_t fresh_var))
      |> add_atom @@ mk_ls fresh_var ls.next 0)
      (* cases where ls has length 0 *)
      :: (f |> add_eq ls.first ls.next |> materialize var)
  (* cases where DLS has minimum length of at least one *)
  | DLS dls when dls.min_len > 0 && var = dls.first ->
      [
        f
        |> add_atom (PointsTo (var, DLS_t (fresh_var, dls.prev)))
        |> add_atom @@ mk_dls fresh_var dls.last var dls.next (dls.min_len - 1);
      ]
  | DLS dls when dls.min_len > 0 && var = dls.last ->
      [
        f
        |> add_atom (PointsTo (var, DLS_t (dls.next, fresh_var)))
        |> add_atom @@ mk_dls dls.first fresh_var dls.prev var (dls.min_len - 1);
      ]
  (* cases where DLS has minimum length of zero -> case split *)
  | DLS dls when var = dls.first ->
      (* length 1+ case *)
      (f
      |> add_atom (PointsTo (var, DLS_t (fresh_var, dls.prev)))
      |> add_atom @@ mk_dls fresh_var dls.last var dls.next 0)
      (* length 0 cases *)
      :: (f |> add_eq dls.first dls.next |> add_eq dls.last dls.prev
        |> materialize var)
  | DLS dls when var = dls.last ->
      (f
      |> add_atom (PointsTo (var, DLS_t (dls.next, fresh_var)))
      |> add_atom @@ mk_dls dls.first fresh_var dls.prev var 0)
      :: (f |> add_eq dls.first dls.next |> add_eq dls.last dls.prev
        |> materialize var)
  (* case where NLS has minimum length of at least one *)
  | NLS nls when nls.min_len > 0 ->
      (* materalization of NLS produces a LS_0+ from fresh_var to `nls.next` *)
      let fresh_ls = SL.Variable.mk_fresh "fresh" Sort.loc_ls in
      [
        f
        |> add_atom (PointsTo (var, NLS_t (fresh_var, fresh_ls)))
        |> add_atom @@ mk_ls fresh_ls nls.next 0
        |> add_atom @@ mk_nls fresh_var nls.top nls.next (nls.min_len - 1);
      ]
  (* case where NLS has minimum length == 0 *)
  | NLS nls ->
      let fresh_ls = SL.Variable.mk_fresh "fresh" Sort.loc_ls in
      (* length 1+ case *)
      (f
      |> add_atom (PointsTo (var, NLS_t (fresh_var, fresh_ls)))
      |> add_atom @@ mk_ls fresh_ls nls.next 0
      |> add_atom @@ mk_nls fresh_var nls.top nls.next 0)
      (* length 0 cases *)
      :: (f |> add_eq nls.first nls.top |> materialize var)
  | Predicate (name, xs) ->
    Config.Self.debug "Unfolding predicate %s %S" name (SL.Variable.show_list xs);
    GlobalSID.cases name (List.map SL.Term.of_var xs)
    |> List.map (fun case -> SL.mk_star [Astral_query.convert f; case])
    |> List.map Astral2Seal.convert
    |> List.map List.hd (* TODO *)
    |> List.filter Astral_query.check_sat
  | _ -> assert false

(** transfer function for function calls *)
let call (lhs_sort : SL.Sort.t) (func : Cil_types.varinfo)
    (args : Formula.var list) (formula : Formula.t) :
    Formula.t list * Formula.var list =
  let get_allocation (init_vars_to_null : bool) =
    let lhs = SL.Variable.mk_fresh "func_ret" lhs_sort in
    let pto =
      let fresh_from_lhs () =
        if init_vars_to_null then Formula.nil
        else SL.Variable.mk_fresh "fresh" lhs_sort
      in
      match () with
      | _ when lhs_sort = SL_builtins.loc_ls || lhs_sort = SL.Sort.loc_nil ->
          Formula.PointsTo (lhs, LS_t (fresh_from_lhs ()))
      | _ when lhs_sort = SL_builtins.loc_dls ->
          Formula.PointsTo (lhs, DLS_t (fresh_from_lhs (), fresh_from_lhs ()))
      | _ when lhs_sort = SL_builtins.loc_nls ->
          Formula.PointsTo
            ( lhs,
              NLS_t (fresh_from_lhs (), SL.Variable.mk_fresh "fresh" Sort.loc_ls)
            )
      | _ ->
          let fields =
            Types.get_struct_def lhs_sort |> MemoryModel.StructDef.get_fields
          in
          let names = List.map MemoryModel.Field.show fields in
          let vars =
            if init_vars_to_null then List.map (fun _ -> Formula.nil) fields
            else
              List.map MemoryModel.Field.get_sort fields
              |> List.map (SL.Variable.mk_fresh (SL.Variable.get_name lhs))
          in
          Formula.PointsTo (lhs, Generic (List.combine names vars))
    in
    let allocation = formula |> Formula.add_atom pto in
    if Config.Svcomp_mode.get () then ([ allocation ], [ lhs ])
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
        formula |> materialize src
        |> List.map (Formula.remove_spatial_from src)
        |> List.map (Formula.add_atom @@ Formula.Freed src)
        |> List.map (fun f -> (f, Formula.nil))
        |> List.split
      with
      | Formula.Bug (Invalid_deref (var, formula), pos) ->
          raise @@ Formula.Bug (Invalid_free (var, formula), pos)
      | e -> raise e)
  | "__VERIFIER_nondet_int", _ -> ([ formula ], [ Formula.nondet ])
  | "__VERIFIER_print_state", _ ->
      Config.Self.result ~current:true "%a" Formula.pp_formula formula;
      ([formula], [Formula.nil])

  | _, args -> Func_call.func_call args func formula lhs_sort
