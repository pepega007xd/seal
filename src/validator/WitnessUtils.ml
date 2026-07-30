open Cil_types
open Filepath

let is_match kf line =
  let (s, e) = match kf.fundec with
    | Definition (_, loc) -> loc
    | Declaration (_, _, _, loc) -> loc
  in
  let s = s.pos_lnum in
  let e = e.pos_lnum in
  s <= line && line <= e

let find_kf_by_line line : Kernel_function.t option =
  Globals.Functions.fold (fun kf acc -> match acc with
    | None when is_match kf line -> Some kf
    | _ -> acc
  ) None

let find_varinfo_by_name (loc : int) name =
  let kf = find_kf_by_line loc in
  match kf with
  | Some kf ->
    Globals.Syntactic_search.find_in_scope ~strict:false name (Whole_function kf)
  | None -> None
