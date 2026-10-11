/-!
# A Merkle tree that mirrors `fastcrypto/src/merkle.rs`

This file transcribes the Merkle tree of
<https://github.com/MystenLabs/fastcrypto/blob/main/fastcrypto/src/merkle.rs>
into Lean. Every definition quotes the Rust it comes from. Read the two side
by side; the point of the exercise is that the Lean *definitions* are
something you can check against the code by eye and by `#eval`, before any
theorem is stated.

Two deliberate modelling choices:

* The hash function `T: HashFunction<32>` becomes a parameter
  `H : List UInt8 → List UInt8`. The Rust pattern
  `update(a); update(b); finalize()` is `H (a ++ b)`. Nothing here knows
  what Blake2b is, so every theorem about this file holds for *every* hash
  function, which is exactly what makes "completeness" provable and
  "binding" not (see Block B).
* Rust stores all nodes in one `Vec<Node>`, level by level. Here the levels
  are kept as a `List (List Node)` and `nodes` is their concatenation. The
  index arithmetic of `get_proof` is then a lookup in one level instead of
  an offset into the flat vector. `n_nodes` is kept and the flat vector is
  recoverable as `MerkleTree.nodes`.

Everything is computable. Run the `#eval`s at the bottom.
-/

namespace Model

/-! ## Constants and nodes

```rust
pub const DIGEST_LEN: usize = 32;
pub const LEAF_PREFIX: [u8; 1] = [0];
pub const INNER_PREFIX: [u8; 1] = [1];
pub const EMPTY_NODE: [u8; DIGEST_LEN] = [0; DIGEST_LEN];

pub enum Node {
    Empty,
    Digest([u8; DIGEST_LEN]),
}
```
-/

/-- A hash function on byte strings. `fastcrypto`'s `HashFunction<32>` with the
`update`/`finalize` API collapsed to one call on the concatenated input. -/
abbrev HashFn := List UInt8 → List UInt8

def DIGEST_LEN : Nat := 32
def LEAF_PREFIX : List UInt8 := [0]
def INNER_PREFIX : List UInt8 := [1]
def EMPTY_NODE : List UInt8 := List.replicate DIGEST_LEN 0

inductive Node where
  | empty
  | digest (val : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/--
```rust
pub fn bytes(&self) -> [u8; DIGEST_LEN] {
    match self {
        Node::Empty => EMPTY_NODE,
        Node::Digest(val) => *val,
    }
}
```
-/
def Node.bytes : Node → List UInt8
  | .empty => EMPTY_NODE
  | .digest val => val

/-! ## Hashing leaves and inner nodes

```rust
pub(crate) fn leaf_hash<T>(input: &[u8]) -> Node {
    let mut hash_fun = T::default();
    hash_fun.update(LEAF_PREFIX);
    hash_fun.update(input);
    hash_fun.finalize().into()
}

fn inner_hash<T>(left: &Node, right: &Node) -> Node {
    let mut hash_fun = T::default();
    hash_fun.update(INNER_PREFIX);
    hash_fun.update(left.bytes());
    hash_fun.update(right.bytes());
    hash_fun.finalize().into()
}
```
-/

def leafHash (H : HashFn) (input : List UInt8) : Node :=
  .digest (H (LEAF_PREFIX ++ input))

def innerHash (H : HashFn) (left right : Node) : Node :=
  .digest (H (INNER_PREFIX ++ left.bytes ++ right.bytes))

/-! ## Errors

The subset of `FastCryptoError` that `merkle.rs` uses. -/

inductive Error where
  | invalidProof
  | invalidInput
  | generalError (msg : String)
  deriving DecidableEq, Repr

/-! ## Building the tree

```rust
pub struct MerkleTree<T = Blake2b256> {
    // The nodes of the Merkle tree are stored in a vector level by level starting with
    // the leaf hashes.
    nodes: Vec<Node>,
    n_leaves: usize,
}

fn build_from_leaf_hashes<I>(iter: I) -> Self {
    let mut nodes = Vec::with_capacity(n_nodes(iter.len()));
    nodes.extend(iter);

    let n_leaves = nodes.len();
    let mut level_nodes = n_leaves;
    let mut prev_level_index = 0;

    // Fill all other nodes of the Merkle Tree
    while level_nodes > 1 {
        if level_nodes % 2 == 1 {
            // We need an empty sibling for the last node on the previous level
            nodes.push(Node::Empty);
            level_nodes += 1;
        }
        let new_level_index = prev_level_index + level_nodes;
        (prev_level_index..new_level_index)
            .step_by(2)
            .for_each(|index| nodes.push(inner_hash::<T>(&nodes[index], &nodes[index + 1])));
        prev_level_index = new_level_index;
        level_nodes /= 2;
    }
    Self { nodes, n_leaves, _hash_type: PhantomData }
}
```

The loop body splits into two steps: pad the current level to even length,
then hash consecutive pairs. `buildLevels` runs the loop and returns the
levels, bottom (leaves) first. The padding `Node::Empty` is stored in the
level, as in Rust.
-/

/-- `if level_nodes % 2 == 1 { nodes.push(Node::Empty) }` -/
def padLevel (level : List Node) : List Node :=
  if level.length % 2 = 1 then level ++ [.empty] else level

/-- `(prev..new).step_by(2).for_each(|i| nodes.push(inner_hash(&nodes[i], &nodes[i + 1])))`,
on a level of even length. `getD` stands in for Rust's indexing; the default is never hit
because the level has been padded. -/
def hashPairs (H : HashFn) (level : List Node) : List Node :=
  (List.range (level.length / 2)).map fun j =>
    innerHash H (level.getD (2 * j) .empty) (level.getD (2 * j + 1) .empty)

/-- The `while level_nodes > 1` loop. Returns the stored levels, leaves first, each already
padded. The last level has at most one node. -/
def buildLevels (H : HashFn) (level : List Node) : List (List Node) :=
  if level.length ≤ 1 then
    [level]
  else
    let padded := padLevel level
    padded :: buildLevels H (hashPairs H padded)
termination_by level.length
decreasing_by
  simp only [hashPairs, List.length_map, List.length_range, padLevel]
  split <;> simp_all <;> omega

structure MerkleTree where
  levels : List (List Node)
  nLeaves : Nat
  deriving Repr

/-- The flat `nodes: Vec<Node>` of the Rust struct. -/
def MerkleTree.nodes (t : MerkleTree) : List Node := t.levels.flatten

def buildFromLeafHashes (H : HashFn) (leafHashes : List Node) : MerkleTree :=
  { levels := buildLevels H leafHashes, nLeaves := leafHashes.length }

/--
```rust
pub fn build_from_serialized<I>(iter: I) -> Self {
    let leaf_hashes = iter.into_iter().map(|leaf| leaf_hash::<T>(leaf.as_ref())).collect();
    Self::build_from_leaf_hashes(leaf_hashes)
}
```
-/
def build (H : HashFn) (leaves : List (List UInt8)) : MerkleTree :=
  buildFromLeafHashes H (leaves.map (leafHash H))

/--
```rust
pub fn root(&self) -> Node {
    self.nodes.last().map_or(Node::Empty, |val| val.clone())
}
```
-/
def MerkleTree.root (t : MerkleTree) : Node :=
  t.nodes.getLast?.getD .empty

/--
```rust
pub(crate) fn n_nodes(n_leaves: usize) -> usize {
    let mut lvl_nodes = n_leaves;
    let mut tot_nodes = 0;
    while lvl_nodes > 1 {
        lvl_nodes += lvl_nodes % 2;
        tot_nodes += lvl_nodes;
        lvl_nodes /= 2;
    }
    tot_nodes + lvl_nodes
}
```
-/
def nNodes (nLeaves : Nat) : Nat :=
  if nLeaves ≤ 1 then nLeaves
  else
    let lvl := nLeaves + nLeaves % 2
    lvl + nNodes (lvl / 2)
termination_by nLeaves
decreasing_by omega

/-! ## Inclusion proofs

```rust
pub struct MerkleProof<T = Blake2b256> {
    /// The sibling hash values on the path from the leaf to the root.
    path: Vec<Node>,
}
```
-/

structure MerkleProof where
  path : List Node
  deriving DecidableEq, Repr

/-!
```rust
pub fn get_proof(&self, leaf_index: usize) -> FastCryptoResult<MerkleProof<T>> {
    if leaf_index >= self.n_leaves {
        return Err(FastCryptoError::GeneralError(format!("Leaf index out of bounds: {}", leaf_index)));
    }
    let mut path = Vec::new();
    let mut level_index = leaf_index;
    let mut n_level = self.n_leaves;
    let mut level_base_index = 0;
    while n_level > 1 {
        // All levels contain an even number of nodes
        n_level = n_level.next_multiple_of(2);
        let sibling_index = if level_index.is_multiple_of(2) {
            level_base_index + level_index + 1
        } else {
            level_base_index + level_index - 1
        };
        path.push(self.nodes[sibling_index].clone());
        // Index of the parent on the next level
        level_index /= 2;
        level_base_index += n_level;
        n_level /= 2;
    }
    Ok(MerkleProof { path })
}
```

`level_base_index + sibling_index` addresses the flat vector; with levels
kept separate it is `level[sibling_index]`. The loop visits every stored
level except the last, which holds the root.
-/

/-- `if level_index.is_multiple_of(2) { level_index + 1 } else { level_index - 1 }` -/
def siblingIndex (levelIndex : Nat) : Nat :=
  if levelIndex % 2 = 0 then levelIndex + 1 else levelIndex - 1

/-- The loop of `get_proof`, over the stored levels. -/
def proofPath : List (List Node) → Nat → List Node
  | [], _ => []
  | [_], _ => []
  | level :: rest, levelIndex =>
      level.getD (siblingIndex levelIndex) .empty :: proofPath rest (levelIndex / 2)

def MerkleTree.getProof (t : MerkleTree) (leafIndex : Nat) : Except Error MerkleProof :=
  if leafIndex ≥ t.nLeaves then
    .error (.generalError s!"Leaf index out of bounds: {leafIndex}")
  else
    .ok { path := proofPath t.levels leafIndex }

/-!
```rust
pub fn compute_root(&self, leaf: &[u8], leaf_index: usize) -> Option<Node> {
    if leaf_index.checked_shr(self.path.len() as u32).is_none_or(|s| s != 0) {
        return None;
    }
    let mut current_hash = leaf_hash::<T>(leaf);
    let mut level_index = leaf_index;
    for sibling in self.path.iter() {
        if level_index.is_multiple_of(2) {
            current_hash = inner_hash::<T>(&current_hash, sibling);
        } else {
            current_hash = inner_hash::<T>(sibling, &current_hash);
        };
        level_index /= 2;
    }
    Some(current_hash)
}
```

`checked_shr` returns `None` when the shift is at least the bit width, and
the test rejects any nonzero result, so the guard is `leaf_index >>> path.len() ≠ 0`.
-/

/-- The `for sibling in self.path` loop. -/
def climb (H : HashFn) : List Node → Node → Nat → Node
  | [], current, _ => current
  | sibling :: rest, current, levelIndex =>
      let next := if levelIndex % 2 = 0 then innerHash H current sibling
                  else innerHash H sibling current
      climb H rest next (levelIndex / 2)

def MerkleProof.computeRoot (H : HashFn) (p : MerkleProof) (leaf : List UInt8)
    (leafIndex : Nat) : Option Node :=
  if leafIndex >>> p.path.length ≠ 0 then none
  else some (climb H p.path (leafHash H leaf) leafIndex)

/--
```rust
pub fn verify_proof(&self, root: &Node, leaf: &[u8], leaf_index: usize) -> FastCryptoResult<()> {
    if self.compute_root(leaf, leaf_index).as_ref() != Some(root) {
        return Err(FastCryptoError::InvalidProof);
    }
    Ok(())
}
```
-/
def MerkleProof.verifyProof (H : HashFn) (p : MerkleProof) (root : Node) (leaf : List UInt8)
    (leafIndex : Nat) : Except Error Unit :=
  if p.computeRoot H leaf leafIndex ≠ some root then .error .invalidProof else .ok ()

/-! ## Sanity checks

A toy hash so that `#eval` produces readable output. It is FNV-1a (64 bit)
repeated four times to fill 32 bytes. The Rust test in `rust/` implements
the same function as a `HashFunction<32>` and prints the same values, so the
definitions above can be compared with the real `MerkleTree` on concrete
inputs. Do not read anything cryptographic into it. -/

def fnv1a64 (bytes : List UInt8) : UInt64 :=
  bytes.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

def toyHash : HashFn := fun bytes =>
  let h := fnv1a64 bytes
  let word := (List.range 8).map fun i => (h >>> (8 * (7 - i)).toUInt64).toUInt8
  word ++ word ++ word ++ word

def Node.hex : Node → String
  | .empty => "Empty"
  | .digest val => String.join (val.take 8 |>.map fun b =>
      let s := String.ofList (Nat.toDigits 16 b.toNat)
      if s.length = 1 then "0" ++ s else s) ++ "…"

def exampleLeaves : List (List UInt8) :=
  ["a", "b", "c", "d", "e"].map fun s => s.toUTF8.toList

/-- Five leaves: levels of length 6 (padded), 3 → 4 (padded), 2, 1. -/
def exampleTree : MerkleTree := build toyHash exampleLeaves

#eval exampleTree.levels.map (·.map Node.hex)
#eval exampleTree.nLeaves
#eval exampleTree.nodes.length
#eval nNodes 5
#eval exampleTree.root.hex
#eval (exampleTree.getProof 2).map fun p => p.path.map Node.hex
#eval (exampleTree.getProof 4).map fun p => p.path.map Node.hex
#eval (exampleTree.getProof 5).map fun p => p.path.map Node.hex
#eval (exampleTree.getProof 2).map fun p =>
  p.verifyProof toyHash exampleTree.root (exampleLeaves.getD 2 []) 2
#eval (exampleTree.getProof 2).map fun p =>
  p.verifyProof toyHash exampleTree.root (exampleLeaves.getD 3 []) 2
#eval (exampleTree.getProof 2).map fun p =>
  p.verifyProof toyHash exampleTree.root (exampleLeaves.getD 2 []) 10

end Model
