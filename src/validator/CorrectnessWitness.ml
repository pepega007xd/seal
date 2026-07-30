open Astral

module RawInvariant = struct

  type t = {
    location: int               (*TODO: Cil_types.location*);
    raw_content: string;
    should_be_inductive : bool;
  }

end

module Invariant = struct

  type t = {
    location: int               (*TODO: Cil_types.location*);
    raw_content: string;
    should_be_inductive : bool;
    content: SL.t;
  }

  let show self =
    let info =
      if self.should_be_inductive then "(inductive) "
      else ""
    in
    Format.asprintf "%s%s" (SL.show self.content) info

end

open Invariant

module InvariantMap = struct

  include Map.Make(Int)

  let show self =
    bindings self
    |> List.map (fun (line, invariant) -> Format.asprintf " - line %d: %s" line (Invariant.show invariant))
    |> String.concat "\n"

end

type witness = {
  (*input_file : string;
  input_file_hash : string;*)

  predicates: InductiveDefinition.t list;
  invariants: Invariant.t InvariantMap.t;
}

let empty = {predicates = []; invariants = InvariantMap.empty}

let pp fmt witness =
  Format.fprintf fmt "@[<v>Predicates:@,";
  List.iter (fun id -> InductiveDefinition.pp fmt id) witness.predicates;
  Format.fprintf fmt "@,Invariants:@,%s@]"
    (InvariantMap.show witness.invariants)
