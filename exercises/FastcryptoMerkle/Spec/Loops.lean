import FastcryptoMerkle.Spec.Model
open Aeneas Aeneas.Std Result
open FastcryptoMerkle FastcryptoMerkle.Spec

/-!
# Specifications of the extracted Merkle functions

One `@[step]` lemma per extracted function, stated against the pure level
model of `Spec/Model.lean`. Loops are proved by `unfold`, `simp only`, `split`,
`step*`, with the loop's own lemma used for the recursive call and a
termination measure. Each lemma is total correctness: no panic, no
divergence, and the stated result.
-/

namespace FastcryptoMerkle.Spec

local notation "Node" => fastcrypto.merkle.Node

theorem spec_eq_ok_iff {α : Type} (m : Result α) (v : α) :
    (m ⦃ r => r = v ⦄) ↔ m = ok v := by
  constructor
  · intro h
    cases m with
    | ret r => simp_all
    | vis i k => simp at h
    | div => simp at h
  · rintro rfl
    simp

/-! ## Hashing -/

/-- Pure leaf digest of a byte vector. -/
def leafDigest (H : HashSpec) (l : alloc.vec.Vec U8) : Node :=
  .Digest (H (fastcrypto.merkle.LEAF_PREFIX.val ++ l.val))

@[step]
theorem leaf_hash_spec (H : HashSpec) (input : Slice U8) :
    fastcrypto.merkle.leaf_hash (hashFunction H) input
      ⦃ n => n = .Digest (H (fastcrypto.merkle.LEAF_PREFIX.val ++ input.val)) ⦄ := by
  simp [leaf_hash_eq]

@[step]
theorem inner_hash_spec (H : HashSpec) (l r : Node) :
    fastcrypto.merkle.inner_hash (hashFunction H) l r ⦃ n => n = innerDigest H l r ⦄ := by
  simp [inner_hash_eq, innerDigest]

/-! ## External models -/

@[step]
theorem vec_as_ref_spec (A : Type) (v : alloc.vec.Vec U8) :
    alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref A v ⦃ s => s.val = v.val ⦄ := by
  simp [alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref, alloc.vec.Vec.deref]

@[step]
theorem vec_reserve_spec {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Usize) :
    alloc.vec.Vec.reserve A v n ⦃ v' => v' = v ⦄ := by
  simp [alloc.vec.Vec.reserve]

/-! ## Leaf hashing loop -/

@[step]
theorem build_from_serialized_slice_loop_spec (H : HashSpec) (leaves : Slice (alloc.vec.Vec U8))
    (acc : alloc.vec.Vec Node) (index : Usize)
    (hidx : index.val ≤ leaves.val.length)
    (hcap : acc.val.length + (leaves.val.length - index.val) ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.build_from_serialized_slice_loop (hashFunction H)
        (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 Global) leaves acc index
      ⦃ out => out.val = acc.val ++ (leaves.val.drop index.val).map (leafDigest H) ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.build_from_serialized_slice_loop
  simp only
  split
  · step*
    case hcap =>
      rw [leaf_hashes1_post]
      simp only [List.length_append, List.length_singleton]
      scalar_tac
    have hd : List.drop index.val leaves.val =
        leaves.val[index.val] :: List.drop (index.val + 1) leaves.val :=
      List.drop_eq_getElem_cons (by scalar_tac)
    rw [out_post, leaf_hashes1_post, index1_post, hd]
    simp only [List.map_cons, List.append_assoc, List.singleton_append, n_post, s_post, t_post,
      leafDigest]
    rfl
  · simp
    scalar_tac
termination_by leaves.val.length - index.val
decreasing_by scalar_tac

/-! ## Node count -/

@[step]
theorem n_nodes_loop_spec (lvl tot : Usize) (h : tot.val + 4 * lvl.val ≤ Usize.max) :
    fastcrypto.merkle.n_nodes_loop lvl tot
      ⦃ l t => (l.val, t.val) = nNodesAux lvl.val tot.val ⦄ := by
  unfold fastcrypto.merkle.n_nodes_loop
  split
  · step*
    rw [l_post, nNodesAux.eq_1 lvl.val tot.val, if_neg (by scalar_tac), lvl_nodes2_post, tot_nodes1_post,
      lvl_nodes1_post, i_post]
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    rw [nNodesAux.eq_1, if_pos (by scalar_tac)]
termination_by lvl.val
decreasing_by scalar_tac

@[step]
theorem n_nodes_spec (n : Usize) (h : 4 * n.val ≤ Usize.max) :
    fastcrypto.merkle.n_nodes n ⦃ r => r.val = nNodes n.val ⦄ := by
  unfold fastcrypto.merkle.n_nodes
  have hb := nNodesAux_bound n.val 0
  step as ⟨lvl_nodes, tot_nodes, hpost⟩
  have h1 : lvl_nodes.val = (nNodesAux n.val 0).1 := by rw [← hpost]
  have h2 : tot_nodes.val = (nNodesAux n.val 0).2 := by rw [← hpost]
  step as ⟨r, hr⟩
  simp only [nNodes]
  omega

/-! ## Builder: inner pairing loop -/

@[step]
theorem build_from_leaf_hashes_loop0_loop0_spec (H : HashSpec) (nodes : alloc.vec.Vec Node)
    (new_level_index index : Usize)
    (hle : index.val ≤ new_level_index.val) (hnew : new_level_index.val ≤ nodes.val.length)
    (heven : (new_level_index.val - index.val) % 2 = 0)
    (hcap : nodes.val.length + (new_level_index.val - index.val) / 2 ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.build_from_leaf_hashes_loop0_loop0 (hashFunction H) nodes
        new_level_index index
      ⦃ out => out.val = nodes.val ++
          hashPairs H ((nodes.val.drop index.val).take (new_level_index.val - index.val)) ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.build_from_leaf_hashes_loop0_loop0
  split
  · step*
    case hcap =>
      rw [nodes1_post]
      simp only [List.length_append, List.length_singleton]
      scalar_tac
    case heven => scalar_tac
    have hm : new_level_index.val - index.val = (new_level_index.val - (index.val + 2)) + 2 := by
      scalar_tac
    have h1 : (nodes.val.drop index.val).take (new_level_index.val - index.val) =
        nodes.val[index.val] :: nodes.val[index.val + 1] ::
          (nodes.val.drop (index.val + 2)).take (new_level_index.val - (index.val + 2)) := by
      rw [hm, List.drop_eq_getElem_cons (l := nodes.val) (i := index.val) (by scalar_tac),
        List.take_succ_cons,
        List.drop_eq_getElem_cons (l := nodes.val) (i := index.val + 1) (by scalar_tac),
        List.take_succ_cons]
    have h2 : (nodes1.val.drop index1.val).take (new_level_index.val - index1.val) =
        (nodes.val.drop (index.val + 2)).take (new_level_index.val - (index.val + 2)) := by
      rw [nodes1_post, index1_post, List.drop_append_of_le_length (by scalar_tac),
        List.take_append_of_le_length (by simp; scalar_tac)]
    have hi : nodes.val[i.val] = nodes.val[index.val + 1] := by
      simp only [i_post]
    rw [out_post, h2, h1, hashPairs_cons_cons, nodes1_post, parent_post, n_post, n1_post, hi]
    simp
  · have h0 : new_level_index.val - index.val = 0 := by scalar_tac
    simp [h0, hashPairs_nil]
termination_by new_level_index.val - index.val
decreasing_by scalar_tac

/-! ## Builder: outer level loop -/

@[step]
theorem build_from_leaf_hashes_loop0_spec (H : HashSpec) (nodes : alloc.vec.Vec Node)
    (level_nodes prev : Usize)
    (hprev : prev.val + level_nodes.val = nodes.val.length)
    (hcap : prev.val + nNodes level_nodes.val ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.build_from_leaf_hashes_loop0 (hashFunction H) nodes level_nodes prev
      ⦃ out => out.val = nodes.val.take prev.val ++ (levels H (nodes.val.drop prev.val)).flatten ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.build_from_leaf_hashes_loop0
  split
  · have hs := nNodes_step level_nodes.val (by scalar_tac)
    have hg := le_nNodes ((level_nodes.val + level_nodes.val % 2) / 2)
    have hL : (nodes.val.drop prev.val).length = level_nodes.val := by simp; scalar_tac
    have hgt : ¬ (nodes.val.drop prev.val).length ≤ 1 := by rw [hL]; scalar_tac
    step*
    split
    · rename_i hi
      have hodd : level_nodes.val % 2 = 1 := by rw [← i_post, hi]; simp
      step as ⟨nodes1, hnodes1⟩
      step as ⟨level_nodes1, hlvl1⟩
      step*
      case heven => scalar_tac
      case hcap =>
        rw [hnodes1]
        simp only [List.length_append, List.length_singleton]
        scalar_tac
      case hprev =>
        rw [nodes2_post, List.length_append, length_hashPairs, hnodes1]
        simp
        scalar_tac
      have hpad : padLevel (nodes.val.drop prev.val) = nodes.val.drop prev.val ++ [.Empty] := by
        unfold padLevel
        rw [if_pos (by rw [hL]; exact hodd)]
      have hn1 : nodes1.val = nodes.val.take prev.val ++ padLevel (nodes.val.drop prev.val) := by
        rw [hnodes1, hpad, ← List.append_assoc, List.take_append_drop]
      have hlen1 : nodes1.val.length = new_level_index.val := by
        rw [hnodes1]; simp; scalar_tac
      have hin : (nodes1.val.drop prev.val).take (new_level_index.val - prev.val) =
          padLevel (nodes.val.drop prev.val) := by
        rw [← hlen1, hn1]
        exact drop_take_prefix _ _ _ (by scalar_tac)
      rw [out_post, nodes2_post, hin, ← hlen1, flatten_levels_unfold H nodes.val prev.val nodes1.val hn1 hgt]
    · rename_i hi
      have heven : level_nodes.val % 2 = 0 := by
        have : i.val ≠ 1 := fun h => hi (by scalar_tac)
        scalar_tac
      step*
      case hprev =>
        rw [nodes2_post, List.length_append, length_hashPairs]
        simp
        scalar_tac
      have hpad : padLevel (nodes.val.drop prev.val) = nodes.val.drop prev.val := by
        unfold padLevel
        rw [if_neg (by rw [hL]; omega)]
      have hlen1 : nodes.val.length = new_level_index.val := by scalar_tac
      have hbound : prev.val ≤ nodes.val.length := by scalar_tac
      have hn1 : nodes.val = nodes.val.take prev.val ++ padLevel (nodes.val.drop prev.val) := by
        rw [hpad, List.take_append_drop]
      have hin : (nodes.val.drop prev.val).take (new_level_index.val - prev.val) =
          padLevel (nodes.val.drop prev.val) := by
        have := drop_take_prefix nodes.val (padLevel (nodes.val.drop prev.val)) prev.val hbound
        rw [← hn1, hlen1] at this
        exact this
      rw [out_post, nodes2_post, hin, ← hlen1, flatten_levels_unfold H nodes.val prev.val nodes.val hn1 hgt]
  · have hle : (nodes.val.drop prev.val).length ≤ 1 := by simp; scalar_tac
    simp only [WP.spec_ok]
    rw [levels_of_le _ _ hle]
    simp
termination_by level_nodes.val
decreasing_by all_goals scalar_tac

/-! ## Builder: top level -/

@[step]
theorem build_from_leaf_hashes_spec (H : HashSpec) (leaf_hashes : alloc.vec.Vec Node)
    (h : 4 * leaf_hashes.val.length ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.build_from_leaf_hashes (hashFunction H) leaf_hashes
      ⦃ t => t.nodes.val = (levels H leaf_hashes.val).flatten ∧
          t.n_leaves.val = leaf_hashes.val.length ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.build_from_leaf_hashes
  have h1 := nNodes_le leaf_hashes.val.length
  have h2 := le_nNodes leaf_hashes.val.length
  step*
  refine ⟨?_, by scalar_tac⟩
  rw [nodes_post, leaf_hashes1_post]
  simp

@[step]
theorem build_from_serialized_slice_spec (H : HashSpec) (leaves : Slice (alloc.vec.Vec U8))
    (h : 4 * leaves.val.length ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.build_from_serialized_slice (hashFunction H)
        (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 Global) leaves
      ⦃ t => t.nodes.val = (levels H (leaves.val.map (leafDigest H))).flatten ∧
          t.n_leaves.val = leaves.val.length ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.build_from_serialized_slice
  step*
  case hcap => simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  case h => rw [leaf_hashes1_post]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; scalar_tac
  have hnew : (alloc.vec.Vec.new Node).val = [] := by simp [alloc.vec.Vec.new]
  simp only [alloc.vec.Vec.with_capacity, hnew, List.nil_append, List.drop_zero] at leaf_hashes1_post
  rw [t_post, t_post1, leaf_hashes1_post]
  simp

/-! ## Root -/

@[step]
theorem node_clone_spec (n : Node) :
    fastcrypto.merkle.Node.Insts.CoreCloneClone.clone n ⦃ r => r = n ⦄ := by
  unfold fastcrypto.merkle.Node.Insts.CoreCloneClone.clone
  cases n with
  | Empty => simp
  | Digest a =>
    step*

@[step]
theorem root_spec (H : HashSpec) (t : fastcrypto.merkle.MerkleTree HashState) :
    fastcrypto.merkle.MerkleTree.root (hashFunction H) t
      ⦃ r => r = t.nodes.val.getLast?.getD .Empty ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.root
  simp only
  split
  · have hnil : t.nodes.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    simp [hnil]
  · step*
    have hi : i.val = t.nodes.val.length - 1 := by scalar_tac
    have hpos : 0 < t.nodes.val.length := by scalar_tac
    rw [r_post, n_post, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some, hi]

/-! ## Inclusion proof generation -/

@[step]
theorem get_proof_loop_spec (H : HashSpec) (v path : alloc.vec.Vec Node)
    (level_index n_level base : Usize) (L : List Node)
    (hL : L.length = n_level.val)
    (hv : v.val.drop base.val = (levels H L).flatten)
    (hidx : level_index.val < L.length)
    (hcap : path.val.length + (levels H L).length ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.get_proof_loop v path level_index n_level base
      ⦃ out => out.val = path.val ++ proofPath (levels H L) level_index.val ⦄ := by
  have hvlen : (v.val.drop base.val).length = v.val.length - base.val := List.length_drop
  have hflat := flatten_levels_length H L
  have hlen_eq : (levels H L).flatten.length = v.val.length - base.val := by rw [← hv, hvlen]
  unfold fastcrypto.merkle.MerkleTree.get_proof_loop
  split
  · have hgt : ¬ L.length ≤ 1 := by scalar_tac
    have hstep := nNodes_step L.length hgt
    have hlev := levels_of_gt H L hgt
    have hPlen := length_padLevel L
    have hPeven := length_padLevel_even L
    have hsl := siblingIndex_lt L level_index.val hidx
    have hPle : (padLevel L).length ≤ (levels H L).flatten.length := by rw [hlev]; simp
    have hlevlen : (levels H L).length = (levels H (hashPairs H (padLevel L))).length + 1 := by
      rw [hlev]; simp
    step*
    case hmax => scalar_tac
    split
    · rename_i hb
      have hev : level_index.val % 2 = 0 := b_post ▸ hb
      have hsibv : siblingIndex level_index.val = level_index.val + 1 := by
        unfold siblingIndex; rw [if_pos hev]
      step*
      case H => exact H
      case L => exact hashPairs H (padLevel L)
      case hL => rw [length_hashPairs, hPlen]; scalar_tac
      case hv =>
        have hb1 : level_base_index1.val = base.val + (padLevel L).length := by
          rw [hPlen]; scalar_tac
        rw [hb1, ← List.drop_drop, hv, hlev, List.flatten_cons, List.drop_left]
      case hidx => rw [length_hashPairs, hPlen]; scalar_tac
      case hcap => rw [path1_post, List.length_append, List.length_singleton]; omega
      all_goals try scalar_tac
      have hn' : n = (padLevel L).getD (siblingIndex level_index.val) .Empty := by
        have hs : sibling_index.val = base.val + siblingIndex level_index.val := by
          rw [hsibv]; scalar_tac
        rw [n_post, List.getElem_eq_iff, hs,
          getElem?_flat_sibling H v.val base.val L hv hgt level_index.val hidx]
      rw [out_post, path1_post, n1_post, hn', hlev, proofPath_cons _ _ (levels_ne_nil H _),
        List.append_assoc, List.singleton_append, level_index1_post]
    · rename_i hb
      have hodd : ¬ level_index.val % 2 = 0 := b_post ▸ hb
      have hsibv : siblingIndex level_index.val = level_index.val - 1 := by
        unfold siblingIndex; rw [if_neg hodd]
      step*
      case H => exact H
      case L => exact hashPairs H (padLevel L)
      case hL => rw [length_hashPairs, hPlen]; scalar_tac
      case hv =>
        have hb1 : level_base_index1.val = base.val + (padLevel L).length := by
          rw [hPlen]; scalar_tac
        rw [hb1, ← List.drop_drop, hv, hlev, List.flatten_cons, List.drop_left]
      case hidx => rw [length_hashPairs, hPlen]; scalar_tac
      case hcap => rw [path1_post, List.length_append, List.length_singleton]; omega
      all_goals try scalar_tac
      have hn' : n = (padLevel L).getD (siblingIndex level_index.val) .Empty := by
        have hs : sibling_index.val = base.val + siblingIndex level_index.val := by
          rw [hsibv]; scalar_tac
        rw [n_post, List.getElem_eq_iff, hs,
          getElem?_flat_sibling H v.val base.val L hv hgt level_index.val hidx]
      rw [out_post, path1_post, n1_post, hn', hlev, proofPath_cons _ _ (levels_ne_nil H _),
        List.append_assoc, List.singleton_append, level_index1_post]
  · have hle : L.length ≤ 1 := by scalar_tac
    simp [levels_of_le _ _ hle, proofPath]
termination_by n_level.val
decreasing_by all_goals scalar_tac

@[step]
theorem get_proof_spec (H : HashSpec) (t : fastcrypto.merkle.MerkleTree HashState) (index : Usize)
    (L : List Node) (hnodes : t.nodes.val = (levels H L).flatten) (hn : t.n_leaves.val = L.length)
    (hidx : index.val < L.length) (hcap : (levels H L).length ≤ Usize.max) :
    fastcrypto.merkle.MerkleTree.get_proof (hashFunction H) t index
      ⦃ r => ∃ p, r = core.result.Result.Ok p ∧ p.path.val = proofPath (levels H L) index.val ⦄ := by
  unfold fastcrypto.merkle.MerkleTree.get_proof
  rw [if_neg (by scalar_tac)]
  have hL : L.length = t.n_leaves.val := hn.symm
  have hv : t.nodes.val.drop (0#usize).val = (levels H L).flatten := by simp [hnodes]
  have hcap' : (alloc.vec.Vec.new Node).val.length + (levels H L).length ≤ Usize.max := by
    simp [alloc.vec.Vec.new]; exact hcap
  step*

/-! ## Slice iterator -/

@[step]
theorem slice_iter_spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter s ⦃ it => it = ⟨s, 0⟩ ⦄ := by
  simp [core.slice.Slice.iter]

theorem slice_iter_next_some {T : Type} (it : core.slice.iter.Iter T) (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it
      ⦃ o it' => o = some it.slice.val[it.i] ∧ it'.slice = it.slice ∧ it'.i = it.i + 1 ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · simp
    rfl
  · exfalso; rename_i hc; exact hc (by scalar_tac)

theorem slice_iter_next_none {T : Type} (it : core.slice.iter.Iter T) (h : ¬ it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it ⦃ o it' => o = none ∧ it' = it ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · exfalso; rename_i hc; exact h (by scalar_tac)
  · simp

/-! ## Root recomputation -/

/-- Pure leaf digest of a byte slice. -/
def leafDigestSlice (H : HashSpec) (leaf : Slice U8) : Node :=
  .Digest (H (fastcrypto.merkle.LEAF_PREFIX.val ++ leaf.val))

@[step]
theorem compute_root_loop_spec (H : HashSpec) (it : core.slice.iter.Iter Node) (cur : Node)
    (li : Usize) :
    fastcrypto.merkle.MerkleProof.compute_root_loop (hashFunction H) it cur li
      ⦃ r => r = climb H (it.slice.val.drop it.i) cur li.val ⦄ := by
  unfold fastcrypto.merkle.MerkleProof.compute_root_loop
  by_cases h : it.i < it.slice.val.length
  · step with (slice_iter_next_some it h) as ⟨o, it1, ho, hs1, hi1⟩
    rw [ho]
    simp only
    step*
    have hd : it.slice.val.drop it.i = it.slice.val[it.i] :: it.slice.val.drop (it.i + 1) :=
      List.drop_eq_getElem_cons h
    split
    · rename_i hb
      have hev : li.val % 2 = 0 := b_post ▸ hb
      step*
      rw [r_post, hs1, hi1, current_hash1_post, level_index1_post, hd]
      simp only [climb, if_pos hev]
    · rename_i hb
      have hodd : ¬ li.val % 2 = 0 := b_post ▸ hb
      step*
      rw [r_post, hs1, hi1, current_hash1_post, level_index1_post, hd]
      simp only [climb, if_neg hodd]
  · step with (slice_iter_next_none it h) as ⟨o, it1, ho, hit1⟩
    rw [ho]
    simp only
    simp [List.drop_eq_nil_of_le (by omega : it.slice.val.length ≤ it.i), climb]
termination_by it.slice.val.length - it.i
decreasing_by all_goals (simp_all; omega)

/-! ## Node equality -/

theorem u8_ne_spec (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ ¬ x = y ⦄ := by
  simp

theorem array_eq_spec {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ r => r ↔ a = b ⦄ := by
  have heq : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a.to_slice b.to_slice := by
    simp [core.array.equality.PartialEqArray.eq, core.slice.cmp.PartialEqSlice.eq, Array.to_slice]
  rw [heq]
  refine WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 a.to_slice
    b.to_slice u8_ne_spec) ?_
  intro r hr
  rw [hr, Slice.eq_iff, Array.eq_iff]
  simp [Array.to_slice]

@[step]
theorem node_eq_spec (a b : Node) :
    fastcrypto.merkle.Node.Insts.CoreCmpPartialEqNode.eq a b ⦃ r => r ↔ a = b ⦄ := by
  unfold fastcrypto.merkle.Node.Insts.CoreCmpPartialEqNode.eq
  cases a <;> cases b <;> simp [fastcrypto.merkle.Node.read_discriminant]
  refine WP.spec_mono (array_eq_spec _ _) ?_
  intro r hr
  simp [hr]

/-! ## Root recomputation and verification -/

@[step]
theorem compute_root_spec (H : HashSpec) (p : fastcrypto.merkle.MerkleProof HashState)
    (leaf : Slice U8) (index : Usize)
    (hlen : p.path.val.length < Usize.numBits) (hidx : index.val < 2 ^ p.path.val.length) :
    fastcrypto.merkle.MerkleProof.compute_root (hashFunction H) p leaf index
      ⦃ r => r = some (climb H p.path.val (leafDigestSlice H leaf) index.val) ⦄ := by
  unfold fastcrypto.merkle.MerkleProof.compute_root
  simp only
  step*
  · exfalso
    have hlenv : p.path.len.val = p.path.val.length := alloc.vec.Vec.len_val _
    have hsz : 2 ^ p.path.val.length < Usize.size := by
      rw [Usize.size_def]; exact Nat.pow_lt_pow_right (by omega) hlen
    have hi1 : i1.val = 2 ^ p.path.val.length := by
      rw [i1_post, hlenv, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hsz]
    scalar_tac
  · rw [current_hash1_post, iter_post, current_hash_post]
    simp [alloc.vec.Vec.deref, leafDigestSlice]

@[step]
theorem slice_get_usize_spec {T : Type} (s : Slice T) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ o => o = s.val[i.val]? ⦄ := by
  simp [core.slice.Slice.get]

@[step]
theorem verify_proof_spec (H : HashSpec) (p : fastcrypto.merkle.MerkleProof HashState)
    (root : Node) (leaf : Slice U8) (index : Usize)
    (hlen : p.path.val.length < Usize.numBits) (hidx : index.val < 2 ^ p.path.val.length) :
    fastcrypto.merkle.MerkleProof.verify_proof (hashFunction H) p root leaf index
      ⦃ r => (climb H p.path.val (leafDigestSlice H leaf) index.val = root →
            r = core.result.Result.Ok ()) ∧
          (climb H p.path.val (leafDigestSlice H leaf) index.val ≠ root →
            r = core.result.Result.Err fastcrypto.error.FastCryptoError.InvalidProof) ⦄ := by
  unfold fastcrypto.merkle.MerkleProof.verify_proof
  step*

end FastcryptoMerkle.Spec
