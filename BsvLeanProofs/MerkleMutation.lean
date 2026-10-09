import BsvLeanProofs.MerkleCounter

/-!
# The mutation flag of the constant-space Merkle computation

`MerkleComputation` reports `mutated` when, while adding a leaf, it combines a
pending subtree hash with an equal hash (the pattern behind CVE-2012-2459). The
comparison is made only in the leaf loop. The final sweep, which combines a
node with itself and then with pending hashes, never compares. This was read
in both the Rust port's `fn compute` and the reference `MerkleComputation`
(bitcoin-sv v1.2.2, `src/consensus/merkle.cpp`): `mutated |= (inner[level] == h)`
appears once, inside the loop over leaves.

What is modelled: the flag, on the slot-list model of `MerkleCounter`.
What is proved: the flag is set exactly when some level of the tree has two
equal adjacent nodes forming a pair in which both nodes are roots of complete
subtrees, that is, subtrees all of whose leaves come from the list. A pair
whose right node contains a duplicated node is not compared.
What is assumed in this file: as in `MerkleCounter`, that the slot list reads
the source's `inner` and `count` correctly. `MerkleLiteral` removes that
assumption for the flag.
-/

namespace Bsv.Merkle

variable {α : Type} [DecidableEq α] (H : α → α → α)

/-- The comparisons made while one leaf is carried up: `inner[level] == hash`
at each occupied level it passes. -/
def insertMut (h : α) : List (Option α) → Bool
  | [] => false
  | none :: _ => false
  | some x :: s => x == h || insertMut (H x h) s

/-- The flag after adding the leaves of `l` to slots `s`. -/
def mutCounter : List α → List (Option α) → Bool
  | [], _ => false
  | a :: t, s => insertMut H a s || mutCounter t (insert H a s)

/-- `mutated`, as the constant-space computation reports it. -/
def mutatedCS (l : List α) : Bool := mutCounter H l []

/-- Some complete pair of this level has two equal nodes. -/
def eqPair : List α → Bool
  | a :: b :: t => a == b || eqPair t
  | _ => false

/-- The tree-level meaning. `pairs` keeps exactly the nodes of the next level
that are roots of complete subtrees, so the recursion visits, at every level,
the pairs of complete subtrees and no others. -/
def mutatedTree : List α → Bool
  | a :: b :: t => eqPair (a :: b :: t) || mutatedTree (pairs H (a :: b :: t))
  | _ => false
termination_by l => l.length
decreasing_by simp only [length_pairs, List.length_cons]; omega

theorem mutCounter_none : ∀ (l : List α) (s : List (Option α)),
    mutCounter H l (none :: s) = (eqPair l || mutCounter H (pairs H l) s)
  | [], _ => by simp [mutCounter, eqPair, pairs]
  | [_], _ => by simp [mutCounter, eqPair, pairs, insertMut]
  | a :: b :: t, s => by
    simp only [mutCounter, insertMut, insert, eqPair, pairs, Bool.false_or,
      mutCounter_none t (insert H (H a b) s)]
    cases (a == b) <;> cases insertMut H (H a b) s <;> cases eqPair t <;> simp

theorem mutCounter_nil (a b : α) (t : List α) :
    mutCounter H (a :: b :: t) [] =
      (eqPair (a :: b :: t) || mutCounter H (pairs H (a :: b :: t)) []) := by
  simp only [mutCounter, insertMut, insert, eqPair, pairs, Bool.false_or, mutCounter_none]
  cases (a == b) <;> cases eqPair t <;> simp

/-- **The flag means what the tree says.** -/
theorem mutatedCS_eq_mutatedTree (l : List α) : mutatedCS H l = mutatedTree H l := by
  unfold mutatedCS
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [mutCounter, mutatedTree]
    | [a], _ => simp [mutCounter, mutatedTree, insertMut]
    | a :: b :: t, hn =>
      rw [mutCounter_nil, mutatedTree]
      congr 1
      exact ih _ (by subst hn; simp only [length_pairs, List.length_cons]; omega) _ rfl

/-- The classic case (CVE-2012-2459), for three leaves: repeating the unpaired
last leaf leaves the root unchanged and sets the flag, whatever `H` is. -/
example (a b c : α) :
    root H [a, b, c, c] = root H [a, b, c] ∧ mutatedCS H [a, b, c, c] = true := by
  constructor
  · simp [root, level]
  · simp [mutatedCS, mutCounter, insertMut, insert]

end Bsv.Merkle
