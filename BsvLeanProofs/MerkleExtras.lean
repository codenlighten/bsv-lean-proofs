import BsvLeanProofs.MerkleVerify

/-!
# Three further facts about the literal branch

* the branch for position 0 does not depend on the first leaf, stated on the
  literal computation (the tree-level statement is `branch_zero_indep`);
* branches of two positions in the same list have the same length;
* a position outside the list produces an empty branch.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

theorem map_some_inj : ∀ a b : List α, a.map some = b.map some → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, map_some_inj a b h.2]

theorem branch0_indep (x y : α) (t : List α) : branch0 H (x :: t) = branch0 H (y :: t) := by
  have h := branch_zero_indep H x y t
  rw [branch_zero, branch_zero] at h
  exact map_some_inj _ _ h

section
variable [Inhabited α]

/-- The literal branch for position 0 does not depend on the first leaf. -/
theorem branchLit_zero_indep (x y : α) (t : List α) :
    branchLit H 0 (x :: t) = branchLit H 0 (y :: t) := by
  rw [branchLit_zero, branchLit_zero, branch0_indep]

end

/-- The number of levels above the leaves. -/
def height : List α → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => 1 + height (level H (a :: b :: t))
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- Every position's branch has one entry per level. -/
theorem length_branchSelf (l : List α) (i : Nat) (hi : i < l.length) :
    (branchSelf H l i).length = height H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l i with
  | _ n ih =>
    match l, hn, hi with
    | [], _, hi => simp at hi
    | [a], _, _ => simp [branchSelf, height]
    | a :: b :: t, hn, hi =>
      have hx : (a :: b :: t)[i]? = some ((a :: b :: t)[i]) := List.getElem?_eq_getElem hi
      obtain ⟨s, hs, _⟩ := sibOrSelf_step H (a :: b :: t) i _ hx
      have hlen := length_level H (a :: b :: t)
      rw [branchSelf, height, hs]
      simp only [List.cons_append, List.nil_append, List.length_cons]
      rw [ih _ (by subst hn; rw [hlen]; simp only [List.length_cons]; omega) _ _
        (by rw [hlen]; simp only [List.length_cons] at hi ⊢; omega) rfl]
      omega

/-- Two positions in the same list have branches of the same length. -/
theorem length_branchSelf_eq (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    (branchSelf H l i).length = (branchSelf H l j).length := by
  rw [length_branchSelf H l i hi, length_branchSelf H l j hj]

/-! ## A position outside the list -/

theorem markAt_ge : ∀ (l : List α) (i : Nat), l.length ≤ i → markAt i l = unm l
  | [], _, _ => by simp [markAt, unm]
  | a :: t, 0, h => by simp at h
  | a :: t, j + 1, h => by
    have := markAt_ge t j (by simpa using h)
    simp [markAt, unm, this]

theorem cntSM_noMarks : ∀ (l : List (α × Bool)) (s : List (Slot α)),
    noMarks l = true → noMarksS s = true → noMarksS (cntSM H l s) = true
  | [], _, _, hs => hs
  | (h, m) :: t, s, hl, hs => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hm, ht⟩ := hl
    subst hm
    exact cntSM_noMarks t _ (by simpa [noMarks] using ht) (insS_noMark H h s hs)

theorem carryB_noMarks : ∀ (s : List (Slot α)) (h : α), noMarksS s = true →
    carryB H h false s = []
  | [], _, _ => rfl
  | none :: s, h, hs => by
    have := carryB_noMarks s (H h h) (by simpa [noMarksS] using hs)
    simp [carryB, this]
  | some (x, mx) :: s, h, hs => by
    simp only [noMarksS, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨hmx, hs'⟩ := hs
    subst hmx
    simp [carryB, push, carryB_noMarks s (H x h) hs']

theorem finishB_noMarks : ∀ s : List (Slot α), noMarksS s = true → finishB H s = []
  | [], _ => rfl
  | none :: s, hs => by
    simpa [finishB] using finishB_noMarks s (by simpa [noMarksS] using hs)
  | some (x, mx) :: s, hs => by
    simp only [noMarksS, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨hmx, hs'⟩ := hs
    subst hmx
    simp [finishB, topB, carryB_noMarks H s (H x x) hs']

section
variable [Inhabited α]

/-- A requested position at or beyond the end of the list gives no branch. -/
theorem branchLit_out_of_range (l : List α) (i : Nat) (hi : l.length ≤ i) :
    branchLit H i l = [] := by
  rw [branchLit_eq_branchCSM, markFrom_le l 0 i (Nat.zero_le _), Nat.sub_zero, markAt_ge l i hi]
  have hn := noMarks_unm l
  simp [branchCSM, cntPM_noMarks H _ [] hn (by simp [noMarksS]),
    finishB_noMarks H _ (cntSM_noMarks H _ [] hn (by simp [noMarksS]))]

end

end Bsv.Merkle
