open Astral
open Astral.Lists
open Formula

(** TODO: do not used SID directly *)
let init ~backend ~encoding ~dump_queries () =
  if Config.Input_witness.is_default () then (
    GlobalSID.register_user_defined ls;
    GlobalSID.register_user_defined ls_two_plus;
    GlobalSID.register_user_defined dls;
    GlobalSID.register_user_defined dls_three_plus;
    GlobalSID.register_user_defined dls_simple;
    GlobalSID.register_user_defined dls_simple_two_plus;
    GlobalSID.register_user_defined nls;
    GlobalSID.register_user_defined nls_two_plus;
  );
  Freed.register ();

  let open SL_builtins in
  let heap_sort =
    HeapSort.of_list
      [
        (loc_ls, LS.struct_ls);
        (loc_dls, DLS.struct_dls);
        (loc_nls, NLS.struct_nls);
      ]
  in
  Solver.init ~dump_queries ~backend ~encoding ~quantifier_encoding:`Direct
    ~use_builtin_defs:false ~source:"seal" ()
  |> Solver.add_heap_sort heap_sort

let is_unconstrained var formula =
  Common.is_fresh_var var
  && Formula.count_relevant_occurences var formula == 1

let[@warning "-8"] convert f =
  let v = SL.Term.of_var in
  let map_atom = function
    | Eq vars when List.exists (SL.Variable.equal Formula.nondet) vars -> SL.emp
    | Eq vars -> SL.mk_eq (List.map v vars)
    | Distinct (lhs, rhs) -> SL.mk_distinct2 (v lhs) (v rhs)
    | Freed var -> SL_builtins.mk_freed (v var)
    | PointsTo (src, LS_t next) -> SL_builtins.mk_pto_ls (v src) ~next:(v next)
    | PointsTo (src, DLS_t (next, prev)) ->
        SL_builtins.mk_pto_dls (v src) ~next:(v next) ~prev:(v prev)
    | PointsTo (src, NLS_t (top, next)) ->
        SL_builtins.mk_pto_nls (v src) ~top:(v top) ~next:(v next)
    | PointsTo (src, Generic vars) ->
        let vars = vars |> List.map snd |> List.map v in
        let struct_def = Types.get_struct_def @@ SL.Variable.get_sort src in
        SL.mk_pto_struct (v src) struct_def vars
    | Predicate (name, params) -> SL.mk_predicate name (List.map SL.Term.of_var params)
    | LS ls -> (
        let first = v ls.first in
        let next = v ls.next in

        let ls_0 = SL_builtins.mk_ls first ~sink:next in
        let ls_1 = SL.mk_star [ ls_0; SL.mk_distinct2 first next ] in
        let ls_2 = SL.mk_predicate "ls_2plus" [first; next] in
        match ls.min_len with 0 -> ls_0 | 1 -> ls_1 | _ -> ls_2)

    | DLS dls when is_unconstrained dls.last f -> (
      (* When the last allocated location in DLS is unconstrained, we
         may use simplified definition of DLS to simplify the formula. *)
      let first = v dls.first in
      let prev = v dls.prev in
      let next = v dls.next in

      let dls_0 = SL.mk_predicate "dls_simple" [ first; next; prev ] in
      let dls_1 = SL.mk_star [ dls_0; SL.mk_distinct2 first next ] in
      let dls_2 = SL.mk_predicate "dls_simple_2plus" [first; next; prev] in
      match dls.min_len with
        | 0 -> dls_0
        | 1 -> dls_1
        | 2 -> dls_2
        | _ -> dls_2 (* TODO: dls_3+ is probably useless here *)
      )
    | DLS dls -> (
        let first = v dls.first in
        let last = v dls.last in
        let prev = v dls.prev in
        let next = v dls.next in

        let dls_0 = SL.mk_predicate "dls" [ first; next; last; prev ] in
        let dls_1 = SL.mk_star [ dls_0; SL.mk_distinct2 first next ] in
        let dls_2 = SL.mk_star [ dls_1; SL.mk_distinct2 first last ] in
        let dls_3 = SL.mk_predicate "dls_3plus" [first; next; last; prev] in

        match dls.min_len with
        | 0 -> dls_0
        | 1 -> dls_1
        | 2 -> dls_2
        | _ -> dls_3)
    | NLS nls -> (
        let first = v nls.first in
        let top = v nls.top in
        let next = v nls.next in
        let nls_0 = SL_builtins.mk_nls first ~sink:top ~bottom:next in
        let nls_1 = SL.mk_star [ nls_0; SL.mk_distinct2 first top ] in
        let nls_2 = SL.mk_predicate "nls_2plus" [first; top; next] in
        match nls.min_len with 0 -> nls_0 | 1 -> nls_1 | _ -> nls_2)
    | IntEq (var, value) ->
        SL.mk_eq2 (v var)
          (SL.Term.mk_smt
             (SMT.of_const (Constant.mk_bitvector_of_int value 32)))
    (* TODO: encode as pointsto or exclude altogether? *)
    | Ref (src, target) ->
        let struct_def = Types.get_struct_def @@ SL.Variable.get_sort src in
        SL.mk_pto_struct (v src) struct_def [ v target ]
  in
  SL.mk_star (List.map map_atom f)
