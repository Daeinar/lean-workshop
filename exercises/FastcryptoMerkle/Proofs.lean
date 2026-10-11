import FastcryptoMerkle.Spec.Loops
import FastcryptoMerkle.Statements
open Aeneas Aeneas.Std Result
open FastcryptoMerkle FastcryptoMerkle.Spec FastcryptoMerkle.Exercises

/-!
# Exercises 2 to 4: proofs

This file is for the LLM. Participants do not edit it by hand. Rules are in
`AGENTS.md`: do not touch `Code/`, `Spec/` or
`exercises/FastcryptoMerkle/Statements.lean`; use the `@[step]` specifications from
`Spec/Loops.lean`; convert `prog = ok v` goals with `rw [← spec_eq_ok_iff]`.
-/

namespace FastcryptoMerkle.Exercises

theorem empty_root : EmptyRootStatement := by
  sorry

theorem out_of_bounds : OutOfBoundsStatement := by
  sorry

theorem roundtrip : RoundtripStatement := by
  sorry

end FastcryptoMerkle.Exercises
