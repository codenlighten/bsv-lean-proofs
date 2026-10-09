import BsvLeanProofs.Splice

/-!
# Properties of the splice opcodes

Theorems about the definitions in `Splice.lean`. Each says what an opcode
returns when it succeeds; the definitions are total, so "succeeds or names an
error" needs no proof.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-! ## OP_SPLIT and OP_CAT -/

/-- OP_SPLIT returns two pieces whose concatenation is the original element,
the left piece below the right one. -/
theorem opSplit_ok (p : Params) (top data : Elem) (st r : Stack)
    (h : opSplit p (top :: data :: st) = .ok r) :
    ∃ k, k ≤ data.length ∧ r = data.drop k :: data.take k :: st := by
  simp only [opSplit] at h
  split at h
  · simp at h
  · rename_i n _
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hc
      simp only [Except.ok.injEq] at h
      refine ⟨n.toNat, by omega, h.symm⟩

/-- Splitting and concatenating again restores the element (after Genesis,
where OP_CAT has no size limit of its own). -/
theorem opSplit_then_opCat (p : Params) (hg : p.afterGenesis = true) (top data : Elem)
    (st r : Stack) (h : opSplit p (top :: data :: st) = .ok r) :
    opCat p r = .ok (data :: st) := by
  obtain ⟨k, _, rfl⟩ := opSplit_ok p top data st r h
  simp [opCat, hg]

/-! ## OP_LEFT, OP_RIGHT, OP_SUBSTR -/

theorem opLeft_ok (p : Params) (l data : Elem) (st r : Stack)
    (h : opLeft p (l :: data :: st) = .ok r) :
    ∃ k, k ≤ data.length ∧ r = data.take k :: st := by
  simp only [opLeft] at h
  split at h
  · simp at h
  · rename_i len _
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hc
      simp only [Except.ok.injEq] at h
      exact ⟨len.toNat, by omega, h.symm⟩

theorem opRight_ok (p : Params) (l data : Elem) (st r : Stack)
    (h : opRight p (l :: data :: st) = .ok r) :
    ∃ k, k ≤ data.length ∧ r = data.drop (data.length - k) :: st := by
  simp only [opRight] at h
  split at h
  · simp at h
  · rename_i len _
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hc
      simp only [Except.ok.injEq] at h
      exact ⟨len.toNat, by omega, h.symm⟩

/-- The first `k` bytes and the last `length - k` bytes make the element. -/
theorem left_append_right (data : Elem) (k : Nat) :
    data.take k ++ data.drop (data.length - (data.length - k)) = data := by
  by_cases hk : k ≤ data.length
  · have : data.length - (data.length - k) = k := by omega
    rw [this, List.take_append_drop]
  · have h1 : data.length - (data.length - k) = data.length := by omega
    rw [h1, List.take_of_length_le (by omega), List.drop_length, List.append_nil]

theorem opSubstr_ok (p : Params) (l o data : Elem) (st r : Stack)
    (h : opSubstr p (l :: o :: data :: st) = .ok r) :
    ∃ off len, off < data.length ∧ off + len ≤ data.length ∧
      r = (data.drop off).take len :: st := by
  simp only [opSubstr] at h
  split at h
  · simp at h
  · rename_i len _
    split at h
    · simp at h
    · rename_i off _
      split at h
      · simp at h
      · rename_i hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt, Int.not_le] at hc
        simp only [Except.ok.injEq] at h
        exact ⟨off.toNat, len.toNat, by omega, by omega, h.symm⟩

/-- An index operand longer than nine bytes is always refused by the three
Chronicle opcodes, whatever it denotes and whatever the era: they use the
narrow reader. -/
theorem chronicleInt_wide (p : Params) (s : Elem) (h : 9 < s.length) :
    chronicleInt p s = .error .scriptNumOverflow ∨
    chronicleInt p s = .error .scriptNumMinEncode := by
  simp only [chronicleInt, scriptNum]
  split
  · left; rfl
  · split
    · right; rfl
    · have hne : s.isEmpty = false := by
        cases s with
        | nil => simp at h
        | cons _ _ => rfl
      simp only [hne, Bool.false_eq_true, if_false, deser123_long s h]
      left; rfl

/-! ## The Chronicle gate -/

/-- For an output created before Chronicle the three opcodes do nothing to the
stack, unless reserved no-ops are discouraged, in which case they are refused. -/
theorem chronicleGate_inactive (p : Params) (op : Params → Stack → Except Err Stack) (st : Stack)
    (h : p.chronicleOps = false) :
    chronicleGate p op st =
      if p.discourageNops then .error .discourageUpgradableNops else .ok st := by
  simp [chronicleGate, h]

theorem chronicleGate_active (p : Params) (op : Params → Stack → Except Err Stack) (st : Stack)
    (h : p.chronicleOps = true) : chronicleGate p op st = op p st := by
  simp [chronicleGate, h]

end Bsv.Splice
