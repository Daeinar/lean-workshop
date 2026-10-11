import Model.Defs

/-!
# Exercise 1: Completeness of the Merkle tree model

Replace the `sorry`s below with the pieces of the statement; `(sorry : Prop)`
marks a condition, a plain `sorry` a value. `README.md` walks
through how the statement is built up from the English description; the names
you need are in `Defs.lean`. Do not touch `Proof.lean`, the LLM fills that in.

You can add `#eval` lines at the end of this file to try things out on the
example tree, e.g. `#eval (build toyHash exampleLeaves).getProof 2`. Remove
them before handing over to the LLM.

## If the LLM does not finish

The usual reason is a statement that is slightly off: a wrong index, a
missing side condition, or a universally quantified proof where the honestly
generated one was meant. Read the LLM's explanation before changing anything.
-/

namespace Model

/-- Completeness of fastcrypto's Merkle tree: for every hash function, every
list of leaves and every position in the list, the proof the tree hands out
for that position verifies against the tree's root. -/
def CompletenessStatement : Prop :=
  ∀ (H : HashFn) (leaves : List (List UInt8)) (i : Nat),
    (sorry : Prop) →                             -- the condition on `i`
    ∃ p : MerkleProof,
      (build H leaves).getProof i = .ok p ∧        -- the tree hands out a proof `p`
      sorry                                      -- `p` verifies: which function, arguments, result?

end Model
