import FastcryptoMerkle.Spec.HashAdapter
open Aeneas Aeneas.Std Result
open FastcryptoMerkle FastcryptoMerkle.Spec

/-!
# Exercises 2 to 4: statements

Replace the `sorry`s below with the pieces of each statement; `(sorry : Prop)`
marks a condition, a plain `sorry` a value. The task
descriptions are in `README.md`. Do not touch `Proofs.lean`, the LLM fills
that in.

Names you will need (from `Code/Funs.lean`, `Code/Types.lean` and
`Spec/HashAdapter.lean`):

* `HashSpec` is the type of hash functions; `hashFunction H` turns an
  `H : HashSpec` into the argument every translated function expects.
* `build_root (hashFunction H) leaves`, `inclusion_roundtrip (hashFunction H)
  leaves index`, `fastcrypto.merkle.MerkleTree.get_proof (hashFunction H) tree
  index` are the translated entry points.
* `Slice (alloc.vec.Vec U8)` is a slice of byte vectors (the leaves), `Usize`
  a machine integer, `Usize.max` the largest one. `.val` gives the underlying
  Lean list or number: `leaves.val : List …`, `index.val : Nat`.
* `fastcrypto.merkle.Node.Empty` is the empty node. A `MerkleTree` has the
  fields `nodes` and `n_leaves`.
* `ok v` means "the Rust code returned `v` without panicking".
  `core.result.Result.Ok x` and `core.result.Result.Err e` are Rust's `Ok`
  and `Err` inside that.
-/

namespace FastcryptoMerkle.Exercises

/-- Exercise 2: the root of the empty tree is `Node.Empty`. -/
def EmptyRootStatement : Prop :=
  ∀ (H : HashSpec) (leaves : Slice (alloc.vec.Vec U8)),
    (sorry : Prop) →                             -- "there are no leaves"
    build_root (hashFunction H) leaves = sorry    -- what comes back?

/-- Exercise 3: `get_proof` on an index at or beyond `n_leaves` returns an `Err`. -/
def OutOfBoundsStatement : Prop :=
  ∀ (H : HashSpec) (tree : fastcrypto.merkle.MerkleTree HashState) (index : Usize),
    (sorry : Prop) →                             -- "the index is out of bounds"
    (sorry : Prop)                               -- "get_proof returns some error"

/-- Exercise 4: build, prove, verify: `inclusion_roundtrip` returns `ok true`
for every in-bounds index. -/
def RoundtripStatement : Prop :=
  ∀ (H : HashSpec) (leaves : Slice (alloc.vec.Vec U8)) (index : Usize),
    (sorry : Prop) →                             -- the conditions (several? chain them with `→`)
    inclusion_roundtrip (hashFunction H) leaves index = sorry

end FastcryptoMerkle.Exercises
