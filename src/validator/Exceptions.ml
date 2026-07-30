open CorrectnessWitness

exception MissingInvariant of int

exception UnknownVariable of RawInvariant.t * string

exception NotInvariant of Formula.state * Invariant.t

exception NotInductive of Invariant.t
