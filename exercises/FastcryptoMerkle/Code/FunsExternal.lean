-- Hand-written models for the external functions that Aeneas left as holes in
-- `FunsExternal_Template.lean`. Translation infrastructure, not exercises.
-- Nothing here is an axiom and nothing is a `sorry`; check with
-- `#print axioms` on any theorem downstream.
import Aeneas
import FastcryptoMerkle.Code.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open FastcryptoMerkle

/-- `impl AsRef<U> for &T`: forwards to the inner instance. -/
@[rust_fun "core::convert::{core::convert::AsRef<&'0 @T, @U>}::as_ref"]
def Shared0T.Insts.CoreConvertAsRef.as_ref
  {T : Type} {U : Type} (AsRefInst : core.convert.AsRef T U) : T → Result U :=
  AsRefInst.as_ref

/-- `impl AsRef<[T]> for [T]`: the identity. -/
@[rust_fun "core::convert::{core::convert::AsRef<[@T], [@T]>}::as_ref"]
def Slice.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type} : Slice T → Result (Slice T) :=
  fun s => ok s

/-- `core::hint::must_use`: the identity. -/
@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type} : T → Result T :=
  fun x => ok x

/-- `alloc::fmt::format`: only used to build the `GeneralError` message in
`get_proof`, which no theorem inspects. Any fixed string is a sound model. -/
@[rust_fun "alloc::fmt::format"]
def alloc.fmt.format : core.fmt.Arguments → Result String :=
  fun _ => ok ""

/-- `Vec::reserve`: capacity is not modelled, so the vector is unchanged. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::reserve"]
def alloc.vec.Vec.reserve
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Std.Usize → Result (alloc.vec.Vec T) :=
  fun v _ => ok v

/-- `impl AsRef<[T]> for Vec<T>`: view the vector as a slice. -/
@[rust_fun
  "alloc::vec::{core::convert::AsRef<alloc::vec::Vec<@T>, [@T]>}::as_ref"]
def alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (Slice T) :=
  fun v => ok (alloc.vec.Vec.deref v)

/-- Default value of the associated constant `HashFunction::OUTPUT_SIZE`,
which fastcrypto defines as `DIGEST_LENGTH`. -/
@[trait_default, rust_const "fastcrypto::hash::HashFunction::OUTPUT_SIZE"]
def fastcrypto.hash.HashFunction.OUTPUT_SIZE.default {Self : Type}
  {DIGEST_LENGTH : Std.Usize} (HashFunctionInst : fastcrypto.hash.HashFunction
  Self DIGEST_LENGTH) : Result Std.Usize :=
  ok DIGEST_LENGTH
