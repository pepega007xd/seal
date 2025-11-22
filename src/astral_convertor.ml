open Astral
open SL_builtins
open Astral.Lists
open Formula

let v = SL.Term.of_var

let mk_pto src vars shared =
  let vars = vars |> List.map v in
  let shared = shared |> List.map snd |> List.map v in
  let struct_def = Types.get_struct_def @@ SL.Variable.get_sort src in
  SL.mk_pto_struct (v src) struct_def (vars @ shared)

let mk_predicate sort vars shared =
  let shared = shared |> List.map snd |> List.map v in
  let struct_def = Types.get_struct_def sort in
  let name = MemoryModel.StructDef.get_name struct_def in
  SL.mk_predicate name (vars @ shared)

let get_name v = SL.Variable.get_sort v |> Sort.name

let convert f =
  let map_atom = function
    | Eq vars -> SL.mk_eq (List.map v vars)
    | Distinct (lhs, rhs) -> SL.mk_distinct2 (v lhs) (v rhs)
    | Freed var -> SL_builtins.mk_freed (v var)
    | PointsTo (src, LS_t next, shared) -> mk_pto src [ next ] shared
    | PointsTo (src, DLS_t (next, prev), shared) ->
        mk_pto src [ next; prev ] shared
    | PointsTo (src, NLS_t (top, next), shared) ->
        mk_pto src [ top; next ] shared
    | PointsTo (src, Generic, shared) -> mk_pto src [] shared
    | LS ls -> (
        let sort = SL.Variable.get_sort ls.first in
        let first = v ls.first in
        let next = v ls.next in

        let ls_0 = mk_predicate sort [ first; next ] ls.shared in
        let ls_1 = SL.mk_star [ ls_0; SL.mk_distinct2 first next ] in
        let ls_2 =
          let n = SL.Term.mk_fresh_var "n" sort in
          SL.mk_star
            [
              mk_pto ls.first [ SL.Term.as_var n ] ls.shared;
              mk_predicate sort [ n; next ] ls.shared;
              SL.mk_distinct [ first; n; next ];
            ]
        in
        match ls.min_len with 0 -> ls_0 | 1 -> ls_1 | _ -> ls_2)
    | DLS dls -> (
        let sort = SL.Variable.get_sort dls.first in
        let first = v dls.first in
        let last = v dls.last in
        let prev = v dls.prev in
        let next = v dls.next in

        let dls_0 = mk_predicate sort [ first; last; prev; next ] dls.shared in
        let dls_1 = SL.mk_star [ dls_0; SL.mk_distinct2 first next ] in
        let dls_2 = SL.mk_star [ dls_1; SL.mk_distinct2 first last ] in
        let dls_3 =
          let n = SL.Term.mk_fresh_var "n" (SL.Term.get_sort first) in
          SL.mk_star
            [
              mk_pto dls.first [ dls.prev; SL.Term.as_var n ] dls.shared;
              mk_predicate sort [ n; last; first; next ] dls.shared;
              SL.mk_distinct2 n next;
              SL.mk_distinct2 last first;
              SL.mk_distinct2 first next;
            ]
        in

        match dls.min_len with
        | 0 -> dls_0
        | 1 -> dls_1
        | 2 -> dls_2
        | _ -> dls_3)
    | NLS nls -> (
        let sort = SL.Variable.get_sort nls.first in
        let next_sort = Types.get_next_sort_of_nls sort in
        let first = v nls.first in
        let top = v nls.top in
        let next = v nls.next in
        let nls_0 = mk_predicate sort [ first; top; next ] nls.shared in
        let nls_1 = SL.mk_star [ nls_0; SL.mk_distinct2 first top ] in
        let nls_2 =
          let t = SL.Term.mk_fresh_var "t" sort in
          let n = SL.Term.mk_fresh_var "n" next_sort in
          SL.mk_star
            [
              mk_pto nls.first [ SL.Term.as_var t; SL.Term.as_var n ] nls.shared;
              mk_predicate sort [ t; top; next ] nls.shared;
              (* shared fields of sublist are not stored for NLS *)
              mk_predicate next_sort [ n; next ] [];
              SL.mk_distinct [ first; top; t ];
            ]
        in
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

let convert_state state = List.map convert state |> SL.mk_or
