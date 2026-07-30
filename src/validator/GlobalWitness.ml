open CorrectnessWitness

let witness = ref CorrectnessWitness.empty

let register_predicates w =
  List.iter Astral.GlobalSID.register_user_defined w.predicates

let set w =
  register_predicates w;
  witness := w

let get_loop_invariant stmt =
  let line = Common.stmt_line stmt in
  InvariantMap.find_opt line !witness.invariants
