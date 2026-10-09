/-!
# The Merkle branch of the first leaf (the coinbase)

Bitcoin's Merkle tree over a list of leaves: at each level adjacent pairs are
combined with `H`, and a level with an odd number of nodes pairs its last node
with itself.

What is modelled: the level-by-level tree as described above, with `H` an
arbitrary function (no property of the hash is used). A branch entry is
`some sibling`, or `none` when the node is paired with itself; `fold` recomputes
a root from a leaf, a branch and an index in the way a verifier does.
What is not modelled: any implementation (for example the constant-space
`MerkleComputation`), and the encoding of "paired with itself" as a zero hash.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-- One level up. -/
def level : List α → List α
  | [] => []
  | [a] => [H a a]
  | a :: b :: t => H a b :: level t

theorem length_level : ∀ l : List α, (level H l).length = (l.length + 1) / 2
  | [] => by simp [level]
  | [_] => by simp [level]
  | _ :: _ :: t => by
    simp only [level, List.length_cons, length_level t]
    omega

/-- The root; `none` only for the empty list. -/
def root : List α → Option α
  | [] => none
  | [a] => some a
  | a :: b :: t => root (level H (a :: b :: t))
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- The sibling of position `i` in a level: `none` when position `i` is the
unpaired last node, which is then combined with itself. -/
def sib (l : List α) (i : Nat) : Option α := l[i ^^^ 1]?

/-- The branch of the leaf at position `i`. -/
def branch : List α → Nat → List (Option α)
  | [], _ => []
  | [_], _ => []
  | a :: b :: t, i => sib (a :: b :: t) i :: branch (level H (a :: b :: t)) (i / 2)
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- One verifier step. -/
def step (h : α) (s : Option α) (i : Nat) : α :=
  match s with
  | none => H h h
  | some x => if i % 2 = 1 then H x h else H h x

/-- Recompute a root from a leaf, its branch and its position. -/
def fold : α → List (Option α) → Nat → α
  | h, [], _ => h
  | h, s :: br, i => fold (step H h s i) br (i / 2)

/-- The first leaf's branch, written without any self-pairing case. -/
def branch0 : List α → List α
  | [] => []
  | [_] => []
  | a :: b :: t => b :: branch0 (level H (a :: b :: t))
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- **A1.** At every level of the first leaf's branch the sibling is the node
at position 1, which exists: the branch of position 0 is `branch0`, entry for
entry, and no entry is a self-pairing. -/
theorem branch_zero (l : List α) : branch H l 0 = (branch0 H l).map some := by
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [branch, branch0]
    | [_], _ => simp [branch, branch0]
    | a :: b :: t, hn =>
      rw [branch, branch0]
      simp only [List.map_cons, sib, Nat.zero_div]
      rw [ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ rfl]
      rfl

theorem branch_zero_no_self_pair (l : List α) : ∀ s ∈ branch H l 0, s.isSome = true := by
  rw [branch_zero]
  simp

/-- **A2.** The first leaf's branch does not depend on the first leaf. -/
theorem branch_zero_indep (x y : α) (t : List α) :
    branch H (x :: t) 0 = branch H (y :: t) 0 := by
  induction hn : t.length using Nat.strongRecOn generalizing t x y with
  | _ n ih =>
    match t, hn with
    | [], _ => simp [branch]
    | b :: t', hn =>
      rw [branch, branch]
      simp only [sib, Nat.zero_div, level]
      congr 1
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ rfl

/-- **A3.** Folding any replacement leaf `x` through the branch computed for
the original first leaf `y`, at index 0, gives the root of the tree in which
`x` replaces `y`. -/
theorem fold_branch_zero (x y : α) (t : List α) :
    some (fold H x (branch H (y :: t) 0) 0) = root H (x :: t) := by
  induction hn : t.length using Nat.strongRecOn generalizing t x y with
  | _ n ih =>
    match t, hn with
    | [], _ => simp [branch, fold, root]
    | b :: t', hn =>
      rw [branch, root]
      simp only [sib, Nat.zero_div, level, fold]
      have hs : step H x ([y, b] ++ t')[0 ^^^ 1]? 0 = H x b := by simp [step]
      simp only [List.cons_append, List.nil_append] at hs
      rw [hs]
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ rfl

end Bsv.Merkle
