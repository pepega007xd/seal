(** Validator's entry point. *)

open Config
open Astral

let run_validation witness_path =
  Self.debug "Validating witness %a" Filepath.pretty_rel witness_path;
  let file = Ast.get () in
  Types.process_types file;

  let w = YamlParser.parse @@ Format.asprintf "%a" Filepath.pretty_abs witness_path in
  Self.debug "Input witness:\n%a" CorrectnessWitness.pp w;
  GlobalWitness.set w;
  Verifier.run_analysis ();
  Self.result "Successful validation"

let validate witness_path =
  try run_validation witness_path with e -> (
    match e with
    | Exceptions.MissingInvariant line ->
      Self.result "Invariant is missing for line %d" line;
      Self.result "Witness validation not succesful"
    | Exceptions.NotInvariant (state, invariant) ->
      Self.result "Formula provided for line %d is not an invariant:" invariant.location;
      Self.result "%s" (SL.show invariant.content);
      Self.debug  "State is: %a" Formula.pp_state state;
      Self.result "Witness rejected"
    | Exceptions.UnknownVariable (invariant, name) ->
      Self.result "Error when parsing invariant for line %d: %s" invariant.location invariant.raw_content;
      Self.result "  Variable %s does not exist in the current context" name
    | Formula.Bug (bug_type, pos) ->
      Self.result "Witness validation not succesful";
      Self.result ~source:pos "%a" Formula.pp_bug_type bug_type
    | e ->
     let backtrace = Printexc.get_backtrace () in
     Common.warning "BACKTRACE: \n%s" backtrace;
     raise e
  )
