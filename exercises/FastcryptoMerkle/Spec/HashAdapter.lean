import Aeneas
import FastcryptoMerkle.Code.Types
import FastcryptoMerkle.Code.FunsExternal
import FastcryptoMerkle.Code.Funs

/-!
# Hash adapter

The extracted Merkle functions are generic over fastcrypto's `HashFunction<32>`
trait, which Aeneas renders as the structure `fastcrypto.hash.HashFunction T 32`
passed to every function. This file instantiates it for an arbitrary pure hash
`H : List U8 → Array U8 32`, using the list of bytes fed so far as the
streaming state: `default` is the empty list, `update` appends, `finalize`
applies `H`.

Theorems about the Merkle code then quantify over `H`. No assumption on `H` is
made here; collision-style hypotheses belong to the individual theorems.

The reduction lemmas at the end turn `leaf_hash` and `inner_hash` into the
pure expressions `H (LEAF_PREFIX ++ input)` and `H (INNER_PREFIX ++ left ++
right)`, which is the only shape later proofs need.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open FastcryptoMerkle

namespace FastcryptoMerkle.Spec

/-- A pure hash from byte strings to 32-byte digests. -/
abbrev HashSpec := List U8 → Array U8 32#usize

/-- Streaming state of the adapter: the bytes fed so far. -/
abbrev HashState := List U8

/-- `HashFunction<32>` instance computing `H` on the concatenation of all `update` inputs. -/
def hashFunction (H : HashSpec) : fastcrypto.hash.HashFunction HashState 32#usize where
  OUTPUT_SIZE := ok 32#usize
  coredefaultDefaultInst := { default := ok [] }
  update := fun {_Data} inst st data => do
    let s ← inst.as_ref data
    ok (st ++ s.val)
  finalize := fun st => ok ⟨H st⟩

/-! ## Reduction lemmas -/

@[simp]
theorem hashFunction_default (H : HashSpec) :
    (hashFunction H).coredefaultDefaultInst.default = ok [] := rfl

@[simp]
theorem hashFunction_finalize (H : HashSpec) (st : HashState) :
    (hashFunction H).finalize st = ok ⟨H st⟩ := rfl

/-- `update` with the array-to-slice `AsRef` instance, as used for the prefixes and node bytes. -/
@[simp]
theorem hashFunction_update_array (H : HashSpec) {N : Usize} (st : HashState) (a : Array U8 N) :
    (hashFunction H).update (Array.Insts.CoreConvertAsRefSlice U8 N) st a = ok (st ++ a.val) := by
  simp [hashFunction, Array.Insts.CoreConvertAsRefSlice, Array.Insts.CoreConvertAsRefSlice.as_ref]

/-- `update` with the shared-reference-to-slice `AsRef` instance, as used for the leaf input. -/
@[simp]
theorem hashFunction_update_slice (H : HashSpec) (st : HashState) (s : Slice U8) :
    (hashFunction H).update
      (Shared0T.Insts.CoreConvertAsRef (Slice.Insts.CoreConvertAsRefSlice U8)) st s =
      ok (st ++ s.val) := by
  simp [hashFunction, Shared0T.Insts.CoreConvertAsRef, Shared0T.Insts.CoreConvertAsRef.as_ref,
    Slice.Insts.CoreConvertAsRefSlice.as_ref]

/-- Pure counterpart of `Node::bytes`. -/
def nodeBytes : fastcrypto.merkle.Node → Array U8 32#usize
  | .Empty => fastcrypto.merkle.EMPTY_NODE
  | .Digest val => val

@[simp]
theorem Node_bytes_eq (n : fastcrypto.merkle.Node) :
    fastcrypto.merkle.Node.bytes n = ok (nodeBytes n) := by
  cases n <;> rfl

/-- `leaf_hash` under the adapter is `H (LEAF_PREFIX ++ input)`. -/
theorem leaf_hash_eq (H : HashSpec) (input : Slice U8) :
    fastcrypto.merkle.leaf_hash (hashFunction H) input =
      ok (.Digest (H (fastcrypto.merkle.LEAF_PREFIX.val ++ input.val))) := by
  simp [fastcrypto.merkle.leaf_hash, fastcrypto.merkle.Node.Insts.CoreConvertFromDigest32.from]

/-- `inner_hash` under the adapter is `H (INNER_PREFIX ++ left ++ right)`. -/
theorem inner_hash_eq (H : HashSpec) (left right : fastcrypto.merkle.Node) :
    fastcrypto.merkle.inner_hash (hashFunction H) left right =
      ok (.Digest (H (fastcrypto.merkle.INNER_PREFIX.val ++ (nodeBytes left).val ++
        (nodeBytes right).val))) := by
  simp [fastcrypto.merkle.inner_hash, fastcrypto.merkle.Node.Insts.CoreConvertFromDigest32.from]

/-- The prefixes as byte lists. -/
theorem LEAF_PREFIX_val : fastcrypto.merkle.LEAF_PREFIX.val = [0#u8] := by
  unfold fastcrypto.merkle.LEAF_PREFIX; rfl

theorem INNER_PREFIX_val : fastcrypto.merkle.INNER_PREFIX.val = [1#u8] := by
  unfold fastcrypto.merkle.INNER_PREFIX; rfl

end FastcryptoMerkle.Spec
