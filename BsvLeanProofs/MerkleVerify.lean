import BsvLeanProofs.MerkleBranchAny

/-!
# A branch verifies against the root, at every position

What is proved, on the tree: folding a leaf through its branch gives the root,
for every position, both with a self-pairing written as `none` (`branch`) and
written as the node itself (`branchSelf`).
What is proved, on the literal computation: the branch that `MerkleComputation`
emits for any position inside the list, folded from that leaf, gives the root
that `MerkleComputation` returns for the same list.
What is not proved here: anything about a branch that was not produced from
the list (soundness against forged branches needs a property of the hash).
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-- The parent of the node at position `i` is the verifier's step from it. -/
theorem level_get : ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x →
    (level H l)[i / 2]? = some (step H x (sib l i) i)
  | [], _, _, h => by simp at h
  | [a], i, x, h => by
    match i, h with
    | 0, h =>
      have : a = x := by simpa using h
      subst this
      simp [level, sib, step]
    | j + 1, h => simp at h
  | a :: b :: t, 0, x, h => by
    have : a = x := by simpa using h
    subst this
    simp [level, sib, step]
  | a :: b :: t, 1, x, h => by
    have : b = x := by simpa using h
    subst this
    simp [level, sib, step]
  | a :: b :: t, j + 2, x, h => by
    have hj : t[j]? = some x := by simpa using h
    have ih := level_get t j x hj
    have hx : (j + 2) ^^^ 1 = (j ^^^ 1) + 2 := by
      rw [xor_one, xor_one]
      by_cases hm : j % 2 = 0
      · have : (j + 2) % 2 = 0 := by omega
        simp [hm, this]
      · have : ¬ (j + 2) % 2 = 0 := by omega
        simp only [hm, this, ite_false]; omega
    have hd : (j + 2) / 2 = j / 2 + 1 := by omega
    have hp : (j + 2) % 2 = j % 2 := by omega
    have hs : sib (a :: b :: t) (j + 2) = sib t j := by simp [sib, hx]
    rw [hs, hd]
    simp only [level, List.getElem?_cons_succ, ih]
    cases sib t j <;> simp [step, hp]

/-- **Every honest branch verifies.** Folding the leaf at position `i` through
its branch, at index `i`, gives the root. -/
theorem fold_branch (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    some (fold H x (branch H l i) i) = root H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l i x with
  | _ n ih =>
    match l, hn, hx with
    | [], _, hx => simp at hx
    | [a], _, hx =>
      match i, hx with
      | 0, hx =>
        have : a = x := by simpa using hx
        subst this
        simp [branch, fold, root]
      | j + 1, hx => simp at hx
    | a :: b :: t, hn, hx =>
      have hg := level_get H (a :: b :: t) i x hx
      rw [branch, root, fold]
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ hg rfl

/-- At one level, the entry of `branchSelf` acts on the verifier exactly as the
entry of `branch` does. -/
theorem sibOrSelf_step (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    ∃ s, sibOrSelf l i = [s] ∧ step H x (some s) i = step H x (sib l i) i := by
  unfold sibOrSelf sib
  cases hs : l[i ^^^ 1]? with
  | some s => exact ⟨s, rfl, rfl⟩
  | none =>
    refine ⟨x, by simp [hx], ?_⟩
    have hlen : i < l.length := by
      rcases Nat.lt_or_ge i l.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx; simp at hx
    have hge : l.length ≤ i ^^^ 1 := by
      rcases Nat.lt_or_ge (i ^^^ 1) l.length with h | h
      · rw [List.getElem?_eq_getElem h] at hs; simp at hs
      · exact h
    have heven : i % 2 = 0 := by
      rw [xor_one] at hge
      by_cases hm : i % 2 = 0
      · exact hm
      · simp only [hm, ite_false] at hge; omega
    simp [step, heven]

/-- The same with a self-pairing written as the node itself, which is the form
`MerkleComputation` emits. -/
theorem fold_branchSelf (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    some (fold H x ((branchSelf H l i).map some) i) = root H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l i x with
  | _ n ih =>
    match l, hn, hx with
    | [], _, hx => simp at hx
    | [a], _, hx =>
      match i, hx with
      | 0, hx =>
        have : a = x := by simpa using hx
        subst this
        simp [branchSelf, fold, root]
      | j + 1, hx => simp at hx
    | a :: b :: t, hn, hx =>
      have hg := level_get H (a :: b :: t) i x hx
      obtain ⟨s, hs1, hs2⟩ := sibOrSelf_step H (a :: b :: t) i x hx
      rw [branchSelf, root, hs1]
      simp only [List.cons_append, List.nil_append, List.map_cons, fold, hs2]
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ hg rfl

section
variable [DecidableEq α] [Inhabited α]

/-- **End to end at every position.** The branch the literal computation emits
for leaf `i`, folded from that leaf at index `i`, gives the root the literal
computation returns. -/
theorem fold_branchLit (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    some (fold H x ((branchLit H i l).map some) i) = rootLit H l := by
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; simp at hx
  rw [branchLit_eq_branchSelf H l i hi, fold_branchSelf H l i x hx, rootLit_eq_root]

end

end Bsv.Merkle
