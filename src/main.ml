open Config
open Dataflow2
open Astral
open Common

let verify () =
  (* run the analysis and catch exceptions representing bug detections *)
  (try
    Verifier.run_analysis ();
    (*produce_correctness_witness ();*)
    Self.result "Successful_verification"
   with e -> (
     let backtrace = Printexc.get_backtrace () in
     Common.warning "BACKTRACE: \n%s" backtrace;

     if !Analysis.unknown_condition_reached then Self.result "Unknown_result";

     match e with
     | Formula.Bug (bug_type, pos) ->
         if Config.Svcomp_mode.get () then Witness.write_witness bug_type pos;
         (* print the type of detected bug *)
         Self.result ~source:pos "%a" Formula.pp_bug_type bug_type
     | e ->
         Common.warning "EXCEPTION: %s" (Printexc.to_string e);
         if not @@ Config.Catch_exceptions.get () then raise e));

  (* dump analysis results *)
  Solver.dump_stats (Option.get !solver);
  Func_call.merge_all_results ();
  Self.result "Astral time: %.2f" !Astral_query.solver_time

let main () =
  Printexc.record_backtrace true;

  (* initialize the solver instance *)
  Astral_query.init ();

  if Config.Input_witness.is_default () then verify ()
  else Validator.validate @@ Config.Input_witness.get ()

(* register the analysis entrypoint into Frama-C  *)
let () =
  Boot.Main.extend (function
    | _ when Print_version.get () -> print_endline "0.1"
    | _ when Enable_analysis.get () -> main ()
    | _ -> ())
