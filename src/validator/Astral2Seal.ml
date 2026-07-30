open Astral
open SL
open MemoryModel

let convert_term t = match SL.Term.view t with
  | Var v -> v
  | _ -> assert false

let convert_target c ys =
  let f i y = (Field.show @@ List.nth (StructDef.get_fields c) i, convert_term y) in
  Formula.Generic (List.mapi f ys)

let convert_atom phi = match SL.view phi with
  | Eq xs -> Formula.Eq (List.map convert_term xs)
  | Distinct [x1; x2] -> Formula.Distinct (convert_term x1, convert_term x2)
  | PointsTo (x, c, ys) -> Formula.PointsTo (convert_term x, convert_target c ys)
  | Predicate (name, ys, _) -> Formula.Predicate (name, List.map convert_term ys)
  | _ -> failwith ("TODO" ^ SL.show phi)

let rec convert_sh phi = match SL.view phi with
  | Emp -> []
  | Star psis -> List.concat_map convert_sh psis
  | Exists (_, psi) -> convert_sh psi
  | _ -> [convert_atom phi]

let rec convert phi = match SL.view phi with
  | Or psis -> List.concat_map convert psis
  | Star _ -> [convert_sh phi]
  | Exists (xs, psi) ->
    assert (List.for_all Common.is_fresh_var xs);
    convert psi
  | _ -> [[convert_atom phi]]
