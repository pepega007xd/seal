open Config
open Astral

(** This modules contains functions and variables used by multiple other modules
    of the analyzer to avoid cyclic dependencies *)

(** Astral solver instance *)
let solver : Solver.solver option ref = ref None

let fail message = Self.fatal ~current:true message
let warning message = Self.warning ~current:true message
let debug message = Self.warning ~current:true message
let unsupported message = Self.not_yet_implemented ~current:true message

let mk_fresh_var_from (base : SL.Variable.t) : SL.Variable.t =
  if SL.Variable.is_nil base then SL.Variable.nil
  else
    SL.Variable.mk_fresh (SL.Variable.get_name base) (SL.Variable.get_sort base)

let is_fresh_var (var : SL.Variable.t) : bool =
  String.contains (SL.Variable.get_name var) '!'

let is_nondet_var (var : SL.Variable.t) : bool =
  String.starts_with (SL.Variable.get_name var) ~prefix:"_nondet"

let is_anchor_var (var : SL.Variable.t) : bool =
  String.contains (SL.Variable.get_name var) '$'

let list_count (elem : 'a) (list : 'a List.t) : int =
  list |> List.filter (( = ) elem) |> List.length

(** Maps a function on each pair in list, if the function returns [Some], the
    pair of values is replaced by the returned value, otherwise the pair is left
    in the list *)
let rec list_map_pairs (f : 'a -> 'a -> 'a option) (list : 'a list) : 'a list =
  let rec map_single (item : 'a) (list : 'a list) : 'a list =
    match list with
    | [] -> [ item ]
    | first :: rest -> (
        match f item first with
        | Some joined -> joined :: rest
        | None -> item :: map_single first rest)
  in

  match list with
  | [] -> []
  | [ one ] -> [ one ]
  | first :: rest ->
      let rest = list_map_pairs f rest in
      map_single first rest

let unique_counter = ref 0

let get_unique_name (name : string) : string =
  unique_counter := !unique_counter + 1;
  name ^ "_" ^ string_of_int !unique_counter

let var_unique_name (var : Cil_types.varinfo) : string =
  let open Cil_types in
  if var.vglob then var.vname
  else match Kernel_function.find_defining_kf var with
    | Some kf -> Format.asprintf "%a#%s" Kernel_function.pretty kf var.vname
    | None -> assert false

let stmt_line stmt =
  let loc = Cil_datatype.Stmt.loc stmt in
  (fst loc).pos_lnum

let pretty_stmt_loc fmt stmt =
  let open Cil_types in
  let open Cil_datatype in
  let stmt_short = match stmt.skind with
    | If _ -> "if"
    | Switch _ -> "switch"
    | Loop _ -> "loop"
    | Block _ -> "block"
    | UnspecifiedSequence _ -> "unspec-seq"
    | _ -> Format.asprintf "%a" Stmt.pretty stmt
  in
  Format.fprintf fmt "%d:%s" (stmt_line stmt) stmt_short

let is_loop stmt =
  let open Cil_types in
  match stmt.skind with Loop _ -> true | _ -> false
