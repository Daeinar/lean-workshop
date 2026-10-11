import FastcryptoMerkle.Spec.HashAdapter
open Aeneas Aeneas.Std Result
open FastcryptoMerkle FastcryptoMerkle.Spec

/-!
# Pure level model of the Merkle tree

Proof device for the loop specifications. The extracted code keeps all nodes
in one flat vector; the invariants are easier to state against the list of
levels that the vector is the concatenation of. Nothing here is executable
in the Rust sense; it is the shape of the loop invariants, written once.

`levels H L` is the list of stored levels for an (unpadded) leaf level `L`,
each already padded to even length, last level of length at most one.
`proofPath` and `climb` mirror `get_proof` and `compute_root`.
`functional_completeness` is the theorem the roundtrip reduces to.
-/

namespace FastcryptoMerkle.Spec

local notation "Node" => fastcrypto.merkle.Node

/-- Pure counterpart of `inner_hash`. -/
def innerDigest (H : HashSpec) (l r : Node) : Node :=
  .Digest (H (fastcrypto.merkle.INNER_PREFIX.val ++ (nodeBytes l).val ++ (nodeBytes r).val))

/-- `if level_nodes % 2 == 1 { nodes.push(Node::Empty) }` -/
def padLevel (L : List Node) : List Node :=
  if L.length % 2 = 1 then L ++ [.Empty] else L

/-- The inner loop of `build_from_leaf_hashes`: hash consecutive pairs of an even-length level. -/
def hashPairs (H : HashSpec) (P : List Node) : List Node :=
  (List.range (P.length / 2)).map fun j =>
    innerDigest H (P.getD (2 * j) .Empty) (P.getD (2 * j + 1) .Empty)

/-- The outer loop: all stored levels, leaves first, each padded. -/
def levels (H : HashSpec) (L : List Node) : List (List Node) :=
  if L.length ≤ 1 then [L]
  else
    let P := padLevel L
    P :: levels H (hashPairs H P)
termination_by L.length
decreasing_by
  simp only [hashPairs, List.length_map, List.length_range, padLevel]
  split <;> simp_all <;> omega

/-- `if level_index.is_multiple_of(2) { +1 } else { -1 }` -/
def siblingIndex (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i - 1

/-- The loop of `get_proof`, over the stored levels. -/
def proofPath : List (List Node) → Nat → List Node
  | [], _ => []
  | [_], _ => []
  | level :: rest, i => level.getD (siblingIndex i) .Empty :: proofPath rest (i / 2)

/-- The loop of `compute_root`. -/
def climb (H : HashSpec) : List Node → Node → Nat → Node
  | [], cur, _ => cur
  | sib :: rest, cur, i =>
      climb H rest (if i % 2 = 0 then innerDigest H cur sib else innerDigest H sib cur) (i / 2)

/-- `root`: last stored node, `Empty` if there is none. -/
def rootOf (ls : List (List Node)) : Node := ls.flatten.getLast?.getD .Empty

/-! ## Basic facts -/

theorem levels_ne_nil (H : HashSpec) (L : List Node) : levels H L ≠ [] := by
  unfold levels; split <;> simp

theorem proofPath_cons (level : List Node) (rest : List (List Node)) (hrest : rest ≠ []) (i : Nat) :
    proofPath (level :: rest) i = level.getD (siblingIndex i) .Empty :: proofPath rest (i / 2) := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons l rest => rfl

theorem length_padLevel_even (L : List Node) : (padLevel L).length % 2 = 0 := by
  unfold padLevel; split
  · simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem length_padLevel (L : List Node) : (padLevel L).length = L.length + L.length % 2 := by
  unfold padLevel; split <;> simp <;> omega

theorem length_le_length_padLevel (L : List Node) : L.length ≤ (padLevel L).length := by
  unfold padLevel; split <;> simp

theorem getD_padLevel (L : List Node) (i : Nat) (hi : i < L.length) :
    (padLevel L).getD i .Empty = L.getD i .Empty := by
  unfold padLevel; split
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · rfl

theorem length_hashPairs (H : HashSpec) (P : List Node) :
    (hashPairs H P).length = P.length / 2 := by
  simp [hashPairs]

theorem getD_hashPairs (H : HashSpec) (P : List Node) (j : Nat) (hj : j < P.length / 2) :
    (hashPairs H P).getD j .Empty =
      innerDigest H (P.getD (2 * j) .Empty) (P.getD (2 * j + 1) .Empty) := by
  rw [List.getD_eq_getElem?_getD]
  simp [hashPairs, hj]

theorem flatten_levels_ne_nil (H : HashSpec) (L : List Node) (hL : L ≠ []) :
    (levels H L).flatten ≠ [] := by
  unfold levels; split
  · simpa
  · simp only [List.flatten_cons, ne_eq, List.append_eq_nil_iff, not_and]
    intro h
    exact absurd h (by unfold padLevel; split <;> simp_all)

/-- One climbing step from position `i` of a padded level lands on position `i / 2` of the next. -/
theorem climb_step (H : HashSpec) (P : List Node) (hP : P.length % 2 = 0) (i : Nat)
    (hi : i < P.length) :
    (if i % 2 = 0 then innerDigest H (P.getD i .Empty) (P.getD (siblingIndex i) .Empty)
      else innerDigest H (P.getD (siblingIndex i) .Empty) (P.getD i .Empty)) =
    (hashPairs H P).getD (i / 2) .Empty := by
  rw [getD_hashPairs H P (i / 2) (by omega)]
  unfold siblingIndex
  split
  · have h1 : 2 * (i / 2) = i := by omega
    rw [h1]
  · have h1 : 2 * (i / 2) = i - 1 := by omega
    have h2 : i - 1 + 1 = i := by omega
    rw [h1, h2]

/-- Completeness over the stored levels, with the index bound `compute_root` checks. -/
theorem levels_complete (H : HashSpec) (L : List Node) :
    ∀ i, i < L.length →
      climb H (proofPath (levels H L) i) (L.getD i .Empty) i = rootOf (levels H L) ∧
      i < 2 ^ (proofPath (levels H L) i).length := by
  induction L using levels.induct H with
  | case1 L hL =>
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨x, rfl⟩ : ∃ x, L = [x] := by
      match L, hL, hi with
      | [x], _, _ => exact ⟨x, rfl⟩
    rw [levels]
    simp [proofPath, climb, rootOf]
  | case2 L hL P ih =>
    intro i hi
    rw [show P = padLevel L from rfl] at ih
    clear P
    have hP : (padLevel L).length % 2 = 0 := length_padLevel_even L
    have hiP : i < (padLevel L).length := Nat.lt_of_lt_of_le hi (length_le_length_padLevel L)
    have hnext : i / 2 < (hashPairs H (padLevel L)).length := by
      rw [length_hashPairs]; omega
    obtain ⟨ih1, ih2⟩ := ih (i / 2) hnext
    rw [levels]
    simp only [hL, ↓reduceIte]
    rw [proofPath_cons _ _ (levels_ne_nil H _)]
    simp only [climb, List.length_cons]
    rw [← getD_padLevel L i hi, climb_step H (padLevel L) hP i hiP]
    refine ⟨?_, ?_⟩
    · rw [ih1]
      unfold rootOf
      rw [List.flatten_cons, List.getLast?_append]
      have hne := flatten_levels_ne_nil H (hashPairs H (padLevel L)) (by
        intro h
        have := congrArg List.length h
        rw [length_hashPairs] at this
        simp at this
        omega)
      rcases hflat : (levels H (hashPairs H (padLevel L))).flatten with _ | ⟨a, rest⟩
      · exact absurd hflat hne
      · simp [List.getLast?_cons]
    · rw [Nat.pow_succ]
      omega

/-! ## Node count

`nNodesAux` mirrors the `n_nodes` loop: `(lvl_nodes, tot_nodes)` after the loop.
`flatten_levels_length` identifies the stored node count with it, and
`nNodes_le` is the bound that rules out `usize` overflow in the builder. -/

def nNodesAux : Nat → Nat → Nat × Nat
  | lvl, tot =>
    if lvl ≤ 1 then (lvl, tot)
    else nNodesAux ((lvl + lvl % 2) / 2) (tot + (lvl + lvl % 2))
termination_by lvl _ => lvl
decreasing_by omega

def nNodes (n : Nat) : Nat := (nNodesAux n 0).2 + (nNodesAux n 0).1

theorem nNodesAux_shift (lvl : Nat) :
    ∀ tot, nNodesAux lvl tot = ((nNodesAux lvl 0).1, (nNodesAux lvl 0).2 + tot) := by
  induction lvl using Nat.strong_induction_on with
  | _ lvl ih =>
    intro tot
    by_cases h : lvl ≤ 1
    · simp [nNodesAux, h]
    · have hm : (lvl + lvl % 2) / 2 < lvl := by omega
      rw [nNodesAux.eq_1 lvl tot, if_neg h]
      conv_rhs => rw [nNodesAux.eq_1 lvl 0, if_neg h]
      rw [ih _ hm (tot + (lvl + lvl % 2)), ih _ hm (0 + (lvl + lvl % 2))]
      simp only [Prod.mk.injEq, true_and]
      omega

theorem nNodes_step (n : Nat) (h : ¬ n ≤ 1) :
    nNodes n = (n + n % 2) + nNodes ((n + n % 2) / 2) := by
  unfold nNodes
  rw [nNodesAux.eq_1 n 0, if_neg h, nNodesAux_shift ((n + n % 2) / 2) (0 + (n + n % 2))]
  omega

theorem flatten_levels_length (H : HashSpec) (L : List Node) :
    (levels H L).flatten.length = nNodes L.length := by
  induction L using levels.induct H with
  | case1 L hL =>
    rw [levels, if_pos hL]
    simp [nNodes, nNodesAux, hL]
  | case2 L hL P ih =>
    rw [show P = padLevel L from rfl] at ih
    clear P
    rw [levels, if_neg hL]
    simp only [List.flatten_cons, List.length_append, ih, length_hashPairs, length_padLevel]
    rw [nNodes_step L.length hL]

theorem nNodesAux_bound (lvl tot : Nat) :
    (nNodesAux lvl tot).2 + (nNodesAux lvl tot).1 ≤ tot + 4 * lvl := by
  induction lvl, tot using nNodesAux.induct with
  | case1 lvl tot h => rw [nNodesAux.eq_1, if_pos h]; omega
  | case2 lvl tot h ih => rw [nNodesAux.eq_1, if_neg h]; omega

theorem nNodes_le (n : Nat) : nNodes n ≤ 4 * n := by
  have := nNodesAux_bound n 0
  unfold nNodes; omega

/-! ## Lemmas for the builder loops -/

theorem hashPairs_nil (H : HashSpec) : hashPairs H [] = [] := by
  simp [hashPairs]

theorem hashPairs_cons_cons (H : HashSpec) (a b : Node) (rest : List Node) :
    hashPairs H (a :: b :: rest) = innerDigest H a b :: hashPairs H rest := by
  unfold hashPairs
  have h : (a :: b :: rest).length / 2 = rest.length / 2 + 1 := by simp; omega
  rw [h, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

theorem levels_of_le (H : HashSpec) (L : List Node) (h : L.length ≤ 1) : levels H L = [L] := by
  rw [levels, if_pos h]

theorem levels_of_gt (H : HashSpec) (L : List Node) (h : ¬ L.length ≤ 1) :
    levels H L = padLevel L :: levels H (hashPairs H (padLevel L)) := by
  rw [levels, if_neg h]

theorem nNodes_le_one (n : Nat) (h : n ≤ 1) : nNodes n = n := by
  simp [nNodes, nNodesAux, h]

theorem le_nNodes (n : Nat) : n ≤ nNodes n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 1
    · rw [nNodes_le_one n h]
    · rw [nNodes_step n h]
      have := ih ((n + n % 2) / 2) (by omega)
      omega

/-- The current level, read back from the flat vector after padding. -/
theorem drop_take_prefix (nodes P : List Node) (prev : Nat) (hprev : prev ≤ nodes.length) :
    ((nodes.take prev ++ P).drop prev).take ((nodes.take prev ++ P).length - prev) = P := by
  have hl : (nodes.take prev).length = prev := by simp [hprev]
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append,
    List.length_append, hl, Nat.add_sub_cancel_left, List.take_length]

/-- One iteration of the outer builder loop, on the flat vector. -/
theorem flatten_levels_unfold (H : HashSpec) (nodes : List Node) (prev : Nat)
    (nodes1 : List Node) (h1 : nodes1 = nodes.take prev ++ padLevel (nodes.drop prev))
    (hgt : ¬ (nodes.drop prev).length ≤ 1) :
    (nodes1 ++ hashPairs H (padLevel (nodes.drop prev))).take nodes1.length ++
      (levels H ((nodes1 ++ hashPairs H (padLevel (nodes.drop prev))).drop nodes1.length)).flatten
    = nodes.take prev ++ (levels H (nodes.drop prev)).flatten := by
  rw [List.take_left, List.drop_left, h1, List.append_assoc, levels_of_gt H _ hgt, List.flatten_cons]

/-! ## Lemmas for the proof-generation loop -/

theorem siblingIndex_lt (L : List Node) (i : Nat) (hi : i < L.length) :
    siblingIndex i < (padLevel L).length := by
  have h1 := length_padLevel L
  have h2 := length_padLevel_even L
  unfold siblingIndex
  split <;> omega

/-- The sibling read from the flat vector is the sibling in the padded current level. -/
theorem getElem?_flat_sibling (H : HashSpec) (v : List Node) (base : Nat) (L : List Node)
    (hv : v.drop base = (levels H L).flatten) (hgt : ¬ L.length ≤ 1) (i : Nat)
    (hi : i < L.length) :
    v[base + siblingIndex i]? = some ((padLevel L).getD (siblingIndex i) .Empty) := by
  have hs := siblingIndex_lt L i hi
  rw [← List.getElem?_drop, hv, levels_of_gt H L hgt, List.flatten_cons,
    List.getElem?_append_left hs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
  rfl

/-! ## Length bounds for the roundtrip -/

theorem length_proofPath (ls : List (List Node)) (hne : ls ≠ []) (i : Nat) :
    (proofPath ls i).length = ls.length - 1 := by
  induction ls generalizing i with
  | nil => exact absurd rfl hne
  | cons level rest ih =>
    cases rest with
    | nil => simp [proofPath]
    | cons l rest' =>
      rw [proofPath_cons _ _ (by simp) i, List.length_cons, ih (by simp)]
      simp

/-- `n ≤ 2^k` leaves give at most `k + 1` levels. -/
theorem length_levels_le (H : HashSpec) (k : Nat) :
    ∀ L : List Node, L.length ≤ 2 ^ k → (levels H L).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro L hL
    rw [levels_of_le H L (by simpa using hL)]
    simp
  | succ k ih =>
    intro L hL
    by_cases h : L.length ≤ 1
    · rw [levels_of_le H L h]; simp
    · rw [levels_of_gt H L h, List.length_cons]
      have := ih (hashPairs H (padLevel L)) (by
        rw [length_hashPairs, length_padLevel]
        rw [Nat.pow_succ] at hL
        omega)
      omega

end FastcryptoMerkle.Spec
