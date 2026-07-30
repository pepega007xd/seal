(* Parse SL formula encoded in Cabs

   TODO: cleanup *)

open Astral
open MemoryModel

open Cabs
open Cil_datatype

(* Global context *)

let params = ref []
let location = ref (-1)
let invariant = ref None

(** Utilities *)

let name_equal str = function
  | (_, (name, _, _, _)) -> String.equal name str

let exp_to_string e = match e.expr_node with
   | VARIABLE name -> name
   | _ -> assert false

let expr_name_equal str e = match e.expr_node with
  | VARIABLE name -> String.equal name str
  | _ -> false

(** Conversion *)

let convert_var ?(prefix="") name =
  (** Each variable in invariant must come from the original C program and
      thus we should be able to locate it somewhere. *)
  let open Cil_types in
  let var = WitnessUtils.find_varinfo_by_name !location name in
  match var with
    | Some var ->
      let sort, _ = Types.get_type_info var.vtype in
      let name = Common.var_unique_name var in
      SL.Term.mk_var (prefix ^ name) sort
    | None ->
      try SL.Term.of_var @@ List.find (fun v -> String.equal (SL.Variable.get_name v) name) !params
      with Not_found -> raise @@ Exceptions.UnknownVariable (Option.get !invariant, name)

let rec convert_term e = match e.expr_node with
  | VARIABLE name when String.equal name "NULL" -> SL.Term.nil
  | VARIABLE name -> convert_var name

  | CONSTANT (CONST_INT  i) -> SL.Term.mk_smt @@ SMT.Arithmetic.mk_const @@ int_of_string i
  (*| CONSTANT (CONST_BOOL b) -> SL.Term.mk_smt @@ SMT.Boolean.mk_const b*)
  | CONSTANT _ -> failwith "unsupported constant"

  | UNARY _ -> failwith "unary"
  | BINARY _ -> failwith "binary"

  | INDEX (base, offset) -> failwith "index"

  | PAREN e -> convert_term e

  | MEMBEROF _ -> failwith "memberof"
  | MEMBEROFPTR (base, field) ->
    let base = convert_term base in
    let field = Field.mk field @@ SL.Term.get_sort base in
    SL.Term.mk_heap_term field base

  | CALL (fn, [what; where], _) when expr_name_equal "at" fn ->
    if expr_name_equal "Pre" where then convert_var ~prefix:"A$" (exp_to_string what)
    else failwith "todo: at"

  | CALL _ -> failwith "call"

  | _ -> failwith @@ Format.asprintf "Unknown term: %a" Cprint.print_expression e

let rec convert e = match e.expr_node with
  | BINARY (EQ, e1, e2) -> SL.mk_eq @@ List.map convert_term [e1; e2]
  | BINARY (NE, e1, e2) -> SL.mk_distinct @@ List.map convert_term [e1; e2]
  | BINARY (AND, e1, e2) -> SL.mk_star @@ List.map convert [e1; e2]
  | BINARY (OR, e1, e2) -> SL.mk_or @@ List.map convert [e1; e2]

  | CALL (exp, [base; size], _) when expr_name_equal "canAccess" exp ->
    let base = convert_term base in
    let sort = SL.Term.get_sort base in
    let cons = Types.get_struct_def sort in
    let fields = StructDef.get_fields cons in
    let rhs = List.map (fun f -> SL.Term.mk_fresh_var "e" @@ Field.get_sort f) fields in
    SL.mk_pto_struct base cons rhs

  | CALL (exp, params, _) ->
    (* Inductive predicate *)
    let name = exp_to_string exp in
    SL.mk_predicate name @@ List.map convert_term params
  | UNARY _ -> failwith "unary"
  | BINARY _ -> failwith "binary"
  | CAST _ -> failwith "cast"
  | PAREN e -> convert e
  | MEMBEROF _ -> failwith "memberof"
  | MEMBEROFPTR _ -> failwith "memberof_ptr"
  | _ -> assert false

let get_formula = function
  | RETURN (exp, _) -> convert exp
  | _ -> assert false

let is_existential var =
  String.contains (SL.Variable.show var) '!'

let map_cases fn phi = match SL.view phi with
  | Or psis -> SL.mk_or @@ List.map fn psis
  | _ -> fn phi

let fn phi : SL.t =
  let vars = SL.free_vars phi in
  let existentials = List.filter is_existential vars in
  SL.mk_exists existentials phi
  |> HeapTermElimination.apply
  (*|> QuantifierElimination.remove_determined*)

let get pos body ps cabs =
  let open CorrectnessWitness in
  params := ps;
  location := pos;
  invariant := Some RawInvariant.{location = pos; raw_content = body; should_be_inductive = false (* not relevant *)};
  List.find_map (function
    | FUNDEF (_, name, block, _, _) when name_equal "main" name ->
      let phi = get_formula @@ (List.hd block.bstmts).stmt_node in
      Option.some @@ map_cases fn phi
    | _ -> None
  ) cabs
  |> Option.get
