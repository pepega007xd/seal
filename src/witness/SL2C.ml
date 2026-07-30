(* TODO: proper handling of nondet *)

open Astral
open Formula

module F = Format

let convert_var v =
  let full_name = SL.Variable.show v in
  match String.split_on_char '#' full_name with
  | _ when SL.Variable.is_nil v -> "NULL"
  | [prefix; name] ->
    if String.contains_from full_name 0 '$'
    then Format.sprintf "\\at(%s, Pre)" name
    else name
  | [name] ->
    if String.contains_from full_name 0 '$'
    then Format.sprintf "\\at(%s, Pre)" name
    else name
  | _ -> assert false

let target_to_fields = function
  | LS_t x -> ["next", x]
  | Generic xs -> xs
  | _ -> assert false

(** For an atom, return its string representation as c expression and set of
    permissions needed to evaluate it. *)
let rec convert_atom = function
  | Eq [x; y] -> Option.some @@ F.sprintf "%s == %s" (convert_var x) (convert_var y)
  | Eq (x :: y :: xs) ->
      Option.some @@ F.sprintf "%s == %s && %s" (convert_var x) (convert_var y) (Option.get @@ convert_atom (Eq (y :: xs)))
  | Distinct (x, y) -> Option.some @@ F.sprintf "%s != %s" (convert_var x) (convert_var y)
  | Freed _ -> None
  | PointsTo (x, cons) ->
    target_to_fields cons
    |> List.map (fun (field, y) -> F.sprintf "%s->%s==%s" (convert_var x) field (convert_var y))
    |> String.concat " &*& "
    |> Option.some
  | Predicate (name, xs) -> Option.some @@ F.sprintf "%s(%s)" name (String.concat ", " @@ List.map convert_var xs)
  | IntEq (var, c) -> Option.some @@ F.sprintf "%s==%d" (convert_var var) c
  (* TODO: will not work with multiple types of lists *)
  (* TODO: bounds *)
  | LS {first; next; _} -> Option.some @@ F.sprintf "ls(%s, %s)" (convert_var first) (convert_var next)
  | _ -> failwith "TODO: DLS, NLS"


let perms_atom = function
  | PointsTo (x, cons) ->
    target_to_fields cons
    |> List.map (fun (field, y) -> F.sprintf "\\canAccess(%s->%s, 1)" (convert_var x) field)
    |> String.concat "&*&"
    |> Option.some
  | _ -> None

let preprocess =
  List.filter_map (function
    | Eq xs ->
      let xs = List.filter (fun v -> not @@ Common.is_nondet_var v) xs in
      (match xs with
      | [] | [_] -> None
      | xs -> Some (Eq xs)
      )
    | Distinct (x, y) when List.exists Common.is_nondet_var [x; y] -> None
    | atom -> Some atom
  )

let convert f =
  let f = preprocess f in
  let close str = "(" ^ str ^ ")" in
  let formula = String.concat " &*& "(* @@ List.map close*) @@ List.filter_map convert_atom f in
  let permissions = String.concat " &*& " (*@@ List.map close*) @@ List.filter_map perms_atom f in
  if permissions = ""
  then  formula
  else F.sprintf "%s &*& %s" formula permissions

