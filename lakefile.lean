import Lake
open Lake DSL

package workshop where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

/-- Aeneas Lean library (brings Mathlib), pinned to the nightly whose binaries
produced `exercises/FastcryptoMerkle/Code`. Lake downloads its prebuilt release
archive, so nothing is compiled from source. -/
require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "aa66752b15d02335f936f607b5ad5b9fecb65b13" / "backends/lean"

/-- Part A (`Model`) and Part B (`FastcryptoMerkle`): what participants work on. -/
@[default_target]
lean_lib Exercises where
  srcDir := "exercises"
  roots := #[`Model, `FastcryptoMerkle]

/-- Reference statements and proofs. `lake build Solutions`. -/
lean_lib Solutions where
  srcDir := "solutions"
  roots := #[`ModelSolution, `AeneasSolution]
