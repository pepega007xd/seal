open Astral

let mk_shared_vars shared =
  List.map MemoryModel.Field.get_sort shared
  |> List.map (SL.Variable.mk "shared")

let register_ls (name : string) (sort : Sort.t)
    (struct_def : MemoryModel.StructDef.t) (shared : MemoryModel.Field.t list) =
  let first = SL.Variable.mk "first" sort in
  let next = SL.Variable.mk "next" sort in
  let shared = mk_shared_vars shared in

  let header = first :: next :: shared in

  let first = SL.Term.of_var first in
  let next = SL.Term.of_var next in
  let shared = List.map SL.Term.of_var shared in

  let predicate =
    Lists.ID.mk name header
    @@ SL.mk_or
         [
           SL.mk_eq [ first; next ];
           SL.mk_exists' [ sort ] (function
             | [ n ] ->
                 SL.mk_star
                   [
                     SL.mk_distinct [ first; next ];
                     SL.mk_pto_struct first struct_def (n :: shared);
                     SL.mk_predicate name (n :: next :: shared);
                   ]
             | _ -> assert false);
         ]
  in
  GlobalSID.register_user_defined predicate;
  (sort, struct_def)

let register_dls (name : string) (sort : Sort.t)
    (struct_def : MemoryModel.StructDef.t) (shared : MemoryModel.Field.t list) =
  let first = SL.Variable.mk "first" sort in
  let last = SL.Variable.mk "last" sort in
  let prev = SL.Variable.mk "prev" sort in
  let next = SL.Variable.mk "next" sort in
  let shared = mk_shared_vars shared in

  let header = first :: last :: prev :: next :: shared in

  let first = SL.Term.of_var first in
  let last = SL.Term.of_var last in
  let prev = SL.Term.of_var prev in
  let next = SL.Term.of_var next in
  let shared = List.map SL.Term.of_var shared in

  let predicate =
    Lists.ID.mk name header
    @@ SL.mk_or
         [
           SL.mk_star [ SL.mk_eq2 first next; SL.mk_eq2 last prev ];
           SL.mk_exists' [ sort ] (function
             | [ n ] ->
                 SL.mk_star
                   [
                     SL.mk_distinct2 first next;
                     SL.mk_distinct2 last prev;
                     SL.mk_pto_struct first struct_def (n :: prev :: shared);
                     SL.mk_predicate name (n :: last :: first :: next :: shared);
                   ]
             | _ -> assert false);
         ]
  in
  GlobalSID.register_user_defined predicate;
  (sort, struct_def)

let register_nls (name : string) (sort : Sort.t)
    (struct_def : MemoryModel.StructDef.t) (shared : MemoryModel.Field.t list) =
  (* HACK: [next] field is passed within [shared] because it is non-recursive type *)
  let next_sort, shared =
    match shared with
    | next :: shared -> (MemoryModel.Field.get_sort next, shared)
    | _ -> assert false
  in
  let first = SL.Variable.mk "first" sort in
  let top = SL.Variable.mk "top" sort in
  let next = SL.Variable.mk "next" next_sort in
  let shared = mk_shared_vars shared in

  let header = first :: top :: next :: shared in

  let first = SL.Term.of_var first in
  let top = SL.Term.of_var top in
  let next = SL.Term.of_var next in
  let shared = List.map SL.Term.of_var shared in

  let predicate =
    Lists.ID.mk name header
    @@ SL.mk_or
         [
           SL.mk_eq [ first; top ];
           SL.mk_exists' [ sort; next_sort ] (function
             | [ t; n ] ->
                 SL.mk_star
                   [
                     SL.mk_distinct [ first; top ];
                     SL.mk_pto_struct first struct_def (t :: n :: shared);
                     SL.mk_predicate name (t :: top :: next :: shared);
                     SL.mk_predicate (Sort.name next_sort) [ n; next ];
                   ]
             | _ -> assert false);
         ]
  in
  GlobalSID.register_user_defined predicate;
  (sort, struct_def)
