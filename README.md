# Lean crypto workshop

In this workshop we prove properties of fastcrypto's Merkle tree in Lean. We
will write the **statements** and an LLM will write the **proofs**. Afterwards
we **check** that what the LLM proved is what we meant.

This workshop has four exercises. Exercise 1 works on a hand-written Lean model
of the Merkle tree. Exercises 2, 3 and 4 work on the actual Rust code that was
translated to Lean by [Aeneas](https://github.com/AeneasVerif/aeneas).

1. **Completeness (Lean model):** A proof that the tree hands out for one of
   its leaves is accepted by the verifier. This exercise is guided.
2. **The empty tree (Aeneas/Rust):** Building a tree from no leaves gives the
   empty root.
3. **Out-of-bounds requests fail (Aeneas/Rust):** Asking for a proof for a
   position the tree does not have returns an error.
4. **Completeness (Aeneas/Rust):** The same property as in exercise 1,
   now for the shipped implementation. Here the machine's integers and the
   possibility of panics enter the statement.

## Setup

1. Install [elan](https://github.com/leanprover/elan) and VS Code with the Lean
   4 extension. Open the `lean-workshop/` directory as a folder in VS Code,
   otherwise the extension does not find the project.
2. In the `lean-workshop/` directory run:

   ```sh
   make setup
   ```

   This downloads Lean 4.31, Mathlib and the Aeneas library. The build ends
   with `declaration uses 'sorry'` warnings which is expected as we will
   address the `sorry` statements in the exercises.
3. Run your favorite LLM coding agent (Claude Code, Cursor, ...) in this
   directory and point it to the `AGENTS.md` file that has some instructions and
   guardrails for the agent.

## Layout

```
lean-workshop/
├── README.md                      This file
├── AGENTS.md                      The rules for the LLM
├── Makefile                       `make` builds, `make check` runs the checklist
├── check.sh                       The script behind `make check`
├── exercises/
│   ├── Model/                     Exercise 1
│   │   ├── Defs.lean              The Merkle tree model (given, do not edit)
│   │   ├── Statements.lean        Your statement goes here
│   │   └── Proof.lean             The LLM's proof goes here
│   └── FastcryptoMerkle/          Exercises 2, 3 and 4
│       ├── Code/                  The Rust code translated to Lean (given, do not edit)
│       ├── Spec/                  Specifications of the translated code (given, do not edit)
│       ├── Statements.lean        Your statements go here
│       └── Proofs.lean            The LLM's proofs go here
└── solutions.tar.gz               Reference statements and proofs; unpack with `make solutions` afterwards
```

## How to approach an exercise

1. Read the code and the Lean definitions side by side.
2. Write the statement first in precise English: for which inputs, under
   which conditions, what exactly is returned.
3. Open the `Statements.lean` file of the exercise. It contains the skeleton
   of the statement with `sorry` placeholders: `(sorry : Prop)` where a
   condition goes, a plain `sorry` where a value goes. Replace them with the
   Lean version of your English sentence. Use the syntax notes below, or ask
   the LLM to translate your sentence literally and to explain every symbol;
   the LLM may help with the syntax, but deciding what the statement says is
   your job. Leave the `sorry` in the proof file alone, that one is for the
   LLM. Run `make` until your statement type-checks. Besides building, `make`
   records your statement so that the check can later tell whether the LLM
   changed it in the proving step.
4. Ask the LLM to prove the exercise, taking into account the rules laid out
   in `AGENTS.md`.
5. Run `make check` and go through the checklist.
6. If the statement has to change, go back to step 2.

Expect several rounds. When the LLM says that the statement is false or that
it cannot prove some condition, read its explanation before changing anything.
This is the exercise working as intended.

To start an exercise over, restore its files from the repository, for example
`git checkout -- exercises/Model/Statements.lean exercises/Model/Proof.lean`.

## Lean syntax for statements

The statements only need the following pieces.

- `∀ (x : T), P` reads "for every `x` of type `T`, `P` holds". Several
  variables: `∀ (x : T) (y : U), P`.
- `∃ x, P` reads "there is an `x` such that `P`". `A ∧ B` is "and",
  `A → B` is "if `A` then `B`". Conditions go in front: `∀ (i : Nat), i < 5 → P i`.
- `a = b` and `a ≠ b` compare values. `f x y` applies `f` to `x` and `y`;
  `t.root` is the same as `MerkleTree.root t`.
- `leaves[i]` is the `i`-th element and needs a hypothesis `i < leaves.length`
  in scope, named like `(hi : i < leaves.length) →`. `leaves.getD i d` returns
  `d` when `i` is out of range and needs no hypothesis.
- In the model (exercise 1), functions that can fail return an `Except`: the
  result is `.ok v` or `.error e`. In the translated Rust code (exercises 2
  to 4), `ok v` means "returned `v` without panicking", and Rust's own `Ok`
  and `Err` appear as `core.result.Result.Ok x` and `core.result.Result.Err e`
  inside it. So "`f x` returns some `Ok` value" is
  `∃ v, f x = ok (core.result.Result.Ok v)`, and "`f x` returns some error" is
  `∃ e, f x = ok (core.result.Result.Err e)` (needed in exercise 3). A
  translated value such as a
  slice or a `Usize` becomes an ordinary Lean list or number with `.val`.
- `#eval e` computes `e` and shows the result in the Infoview; `#check e`
  shows its type. Both are commands you can add anywhere in a file.

## Checklist

Go through this after every round of edits and interactions with your LLM
agent. `make check` covers items 1 to 3.

1. **The statement is unchanged.** The given files and your statement are
   exactly as before the LLM ran. If they are not, the LLM edited them:
   restore them and decide whether the change was a correction or a
   weakening. If you never ran `make` after writing the statement, the check
   prints your statements instead; compare them with what you wrote.
2. **No `sorry` is left** in the proof file.
3. **Only allowed axioms are used.** These are `propext`, `Classical.choice`,
   `Quot.sound`, and in Exercises 2 to 4 also `Aeneas.Std.core.fmt.Formatter`
   (explained at the end of the exercises). `sorryAx` means a hidden `sorry`.
   `Lean.ofReduceBool` means `native_decide`. Anything else is an axiom the
   LLM added.
4. **The hypotheses are satisfiable.** Write down one concrete input that
   meets all hypotheses. A theorem whose hypotheses never hold is true and
   worthless.
5. **The conclusion is as strong as you meant.** Typical weak spots: "if
   `f x` returns `p` then `P p`" is satisfied for free when `f x` fails,
   whereas "`f x` returns some `p` and `P p`" is not; "the result is not the
   error `e`" is weaker than "the result is `Ok ()`"; and a statement about
   one fixed hash function says nothing about the algorithm.

## Exercise 1: Completeness of the Merkle tree model (guided)

In this exercise we work with a hand-written Lean model of fastcrypto's Merkle
tree, `exercises/Model/Defs.lean`. Each definition sits under the Rust code it
transcribes. The hash function is a parameter `H`, so whatever we prove holds
for every hash function. We prove completeness: the inclusion proof that the
tree hands out for any of its leaves verifies against the tree's root. This
exercise is guided: the statement is derived below, step by step, so that the
workflow and the syntax are familiar before exercises 2 to 4.

1. Open `exercises/Model/Defs.lean` in VS Code and read it next to
   `fastcrypto/src/merkle.rs`. The lines at the end of the file that start
   with `#eval` compute something on a small example tree, for instance the
   root or an inclusion proof. Place the cursor on such a line: the result
   appears in the Lean Infoview panel on the right (if the panel is not
   visible, open it with the ∀ button in the top right corner of the editor).
   Compare the results with what the Rust code would do.

2. The property in English: *for every hash function `H`, every list of
   leaves, and every position `i` in that list, building the tree from the
   leaves and asking for the proof at position `i` returns a proof `p`, and
   verifying `p` against the root of that tree, for the leaf at position `i`,
   is accepted.* Translate it phrase by phrase:

   - "for every hash function `H`": `∀ (H : HashFn),`. `HashFn` is the type
     of hash functions in `Defs.lean`.
   - "every list of leaves": `(leaves : List (List UInt8))`. A leaf is a byte
     string, so a list of leaves is a list of byte lists.
   - "every position `i` in that list": `(i : Nat)` together with the
     condition `i < leaves.length`. Without the condition the sentence is
     about positions that do not exist, `getProof` fails there, and the
     statement is false. Name the condition, `(hi : i < leaves.length) →`,
     because `leaves[i]` below needs it.
   - "building the tree": `build H leaves`.
   - "asking for the proof at `i` returns a proof `p`": `getProof` returns an
     `Except`, so success is `.ok p`: `∃ p : MerkleProof,
     (build H leaves).getProof i = .ok p`.
   - "verifying `p` against the root, for the leaf at `i`, is accepted":
     `p.verifyProof H (build H leaves).root leaves[i] i = .ok ()`. Look up
     the argument order of `verifyProof` in `Defs.lean`.

   Put together:

   ```lean
   def CompletenessStatement : Prop :=
     ∀ (H : HashFn) (leaves : List (List UInt8)) (i : Nat),
       (hi : i < leaves.length) →
       ∃ p : MerkleProof,
         (build H leaves).getProof i = .ok p ∧
         p.verifyProof H (build H leaves).root leaves[i] i = .ok ()
   ```

3. Fill the skeleton in `exercises/Model/Statements.lean` accordingly and run
   `make` until it type-checks. Before handing over to the LLM, test the
   pieces on the example tree: `Defs.lean` defines `toyHash` and
   `exampleLeaves` for this. Add lines such as
   `#eval (build toyHash exampleLeaves).getProof 2` at the end of
   `Statements.lean`, read the results in the Infoview, and delete the lines
   again.

4. Ask the LLM to prove exercise 1, run `make check`, and go through the
   checklist. For item 4, the test from step 3 becomes one Lean line that
   applies the proved theorem to the example tree:

   ```lean
   example : ∃ p, (build toyHash exampleLeaves).getProof 2 = .ok p ∧
       p.verifyProof toyHash (build toyHash exampleLeaves).root (exampleLeaves[2]) 2 = .ok () :=
     Model.completeness toyHash exampleLeaves 2 (by decide)
   ```

Two of the choices above were real decisions, and they return in exercise 4:
the bound on `i`, and `∃ p, … = .ok p ∧ …` rather than "for every `p` that
`getProof` might return", which would be satisfied even if `getProof` always
failed.

## Exercises 2 to 4: The actual Rust code

In these exercises we work with the Rust code itself.
`exercises/FastcryptoMerkle/Code/Funs.lean` is fastcrypto's `merkle` module
(commit `d7822bf`) translated to Lean by Aeneas. Compared to the model, the
translation shows what the machine really does: every function returns a
`Result` because Rust can panic, integers are machine integers that can
overflow or wrap, indexing is bounds-checked, loops are recursive functions
ending in `_loop`, and nothing can be run with `#eval`. The hash function is
a trait argument; we pass `hashFunction H` from `Spec/HashAdapter.lean` for an
arbitrary `H`. The files in `Spec/` are given: one specification per
translated function and the facts about the tree that the proofs need. We
write our statements in the form `prog = ok v`, which reads "the Rust code
returns `v` and does not panic".

Read `Code/Funs.lean` once next to `merkle.rs`. The three statements go into
`exercises/FastcryptoMerkle/Statements.lean`, which contains a skeleton for
each and lists the Lean names you need. As in exercise 1, write each
statement in English first, then fill the skeleton.

### Exercise 2: The root of the empty tree

In this exercise we prove that building a tree from no leaves gives the root
`Node.Empty`. The hash function plays no role in the result, so the exercise
is about getting used to the translated code.

Write `EmptyRootStatement`. Express "no leaves" as the hypothesis
`leaves.val = []`.

### Exercise 3: An out-of-bounds proof request fails

In this exercise we prove that `get_proof` returns an `Err` whenever the index
is at or beyond `n_leaves`. A value of the Lean type `MerkleTree` is just a
record of a `nodes` list and a number `n_leaves`. Most such records were never
produced by the builder; `n_leaves` may claim ten leaves while `nodes` holds
three. The statement holds for all of them, because `get_proof` checks the
index before it touches `nodes`.

Write `OutOfBoundsStatement`, quantifying over every value of type
`MerkleTree`, not only over trees that came out of the builder. Once it is
proved, ask yourself whether the converse holds: does an in-bounds index
always give `Ok`? For an arbitrary record it does not, because with
inconsistent `nodes` and `n_leaves` the indexing panics. That direction needs
a tree that was actually built, which is exercise 4.

### Exercise 4: Completeness of the Rust code (the prove-verify roundtrip)

In this exercise we prove completeness again, this time for the shipped code:
for every hash function, every list of leaves and every in-bounds index,
`inclusion_roundtrip` returns `ok true`. The function builds the tree, asks
for the proof at the index and verifies it against the root, so this is the
statement of exercise 1 with the model replaced by the translated Rust. The
shape of the statement is the same; what differs is what the Rust code does
that the model did not, and that is where we go back and forth with the LLM.

Write `RoundtripStatement`. Expect two rounds with the LLM:

1. The LLM should report that the statement is false without a bound on the
   number of leaves: `compute_root` rejects paths with `usize::BITS` or more
   siblings, and the node count can overflow. Add a hypothesis that bounds
   the number of leaves relative to the largest machine integer, for example
   `4 * leaves.val.length ≤ Usize.max`. The factor does not matter; having a
   bound does.
2. The LLM must use `Spec/` instead of re-proving the loops. If it is stuck,
   give these hints one at a time:
   - Start with `rw [← spec_eq_ok_iff]`, `unfold inclusion_roundtrip`, `step*`
     and look at the remaining goals.
   - The remaining goals are about lengths. Establish `length_levels_le`,
     `length_proofPath` and `levels_complete` from `Spec/Model.lean` as
     `have`s before `step*`.
   - The last goal compares the recomputed root with the stored root. Both
     are `rootOf (levels H L)` with `L` the hashed leaves; the verified leaf
     is `L.getD index .Empty`.

If the hints do not land, unpack the solutions with `make solutions` and read
`solutions/AeneasSolution/Proofs.lean`.

Two notes for the checklist. In exercises 3 and 4, `#print axioms` lists
`Aeneas.Std.core.fmt.Formatter`. This is the Aeneas library's placeholder for
Rust's `Formatter` type, reached through the `format!` in `get_proof`'s error
message; it is a type, not a proposition, and the check allows it. For item 4
there is no `#eval` here: write the concrete input down and prove the bounds
with `decide` or `omega`.
