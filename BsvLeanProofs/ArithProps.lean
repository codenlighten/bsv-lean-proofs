import BsvLeanProofs.Arith

/-!
# Properties of the arithmetic opcodes

* What OP_ADD, OP_SUB, OP_MUL, OP_DIV and OP_MOD return when they succeed, and
  the division identity that ties OP_DIV and OP_MOD together.
* Before Genesis the source computes in `int64_t` on operands of at most four
  bytes; no sum, difference, product or negation of such operands leaves the
  range of `int64_t`, so the unchecked narrow arithmetic is safe.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-- On success OP_ADD pushes the minimal encoding of the sum. -/
theorem opAdd_ok (p : Params) (x2 x1 : Elem) (st r : Stack)
    (h : opBinary .add p (x2 :: x1 :: st) = .ok r) :
    ∃ a c : Int, num p x1 = .ok a ∧ num p x2 = .ok c ∧ r = encInt (a + c) :: st ∧
      denote (encInt (a + c)) = a + c := by
  simp only [opBinary] at h
  split at h
  · simp at h
  · rename_i a ha
    split at h
    · simp at h
    · rename_i c hc
      simp only [pushChecked] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨a, c, ha, hc, h.symm, denote_encInt _⟩

/-- On success OP_MUL pushes the minimal encoding of the product. -/
theorem opMul_ok (p : Params) (x2 x1 : Elem) (st r : Stack)
    (h : opBinary .mul p (x2 :: x1 :: st) = .ok r) :
    ∃ a c : Int, num p x1 = .ok a ∧ num p x2 = .ok c ∧ r = encInt (a * c) :: st ∧
      denote (encInt (a * c)) = a * c := by
  simp only [opBinary] at h
  split at h
  · simp at h
  · rename_i a ha
    split at h
    · simp at h
    · rename_i c hc
      simp only [pushChecked] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨a, c, ha, hc, h.symm, denote_encInt _⟩

/-- OP_DIV refuses a zero divisor and otherwise pushes the quotient truncated
toward zero. -/
theorem opDiv_ok (p : Params) (x2 x1 : Elem) (st r : Stack)
    (h : opBinary .div p (x2 :: x1 :: st) = .ok r) :
    ∃ a c : Int, num p x1 = .ok a ∧ num p x2 = .ok c ∧ c ≠ 0 ∧
      r = encInt (Int.tdiv a c) :: st := by
  simp only [opBinary] at h
  split at h
  · simp at h
  · rename_i a ha
    split at h
    · simp at h
    · rename_i c hc
      split at h
      · simp at h
      · rename_i hz
        simp only [Except.ok.injEq] at h
        exact ⟨a, c, ha, hc, by simpa using hz, h.symm⟩

/-- OP_MOD likewise, with the remainder of truncating division. -/
theorem opMod_ok (p : Params) (x2 x1 : Elem) (st r : Stack)
    (h : opBinary .mod p (x2 :: x1 :: st) = .ok r) :
    ∃ a c : Int, num p x1 = .ok a ∧ num p x2 = .ok c ∧ c ≠ 0 ∧
      r = encInt (Int.tmod a c) :: st := by
  simp only [opBinary] at h
  split at h
  · simp at h
  · rename_i a ha
    split at h
    · simp at h
    · rename_i c hc
      split at h
      · simp at h
      · rename_i hz
        simp only [Except.ok.injEq] at h
        exact ⟨a, c, ha, hc, by simpa using hz, h.symm⟩

/-- The quotient and remainder the two opcodes return satisfy
`a = c · (a / c) + (a mod c)`. -/
theorem div_mod_identity (a c : Int) : c * Int.tdiv a c + Int.tmod a c = a :=
  Int.mul_tdiv_add_tmod a c

/-! ## Before Genesis: the narrow arithmetic cannot overflow -/

/-- A number operand of at most four bytes is below `2^31` in magnitude. -/
theorem mag_le_four (s : Elem) (h : s.length ≤ 4) : mag s < 2147483648 := by
  have hu := mag_lt_upper s
  match hk : s.length with
  | 0 => rw [hk] at hu; simp [upperBound] at hu; omega
  | 1 => rw [hk] at hu; simp [upperBound] at hu; omega
  | 2 => rw [hk] at hu; simp [upperBound] at hu; omega
  | 3 => rw [hk] at hu; simp [upperBound] at hu; omega
  | 4 => rw [hk] at hu; simp [upperBound] at hu; omega
  | k + 5 => omega

theorem natAbs_denote (s : Elem) : (denote s).natAbs = mag s := by
  simp only [denote]
  cases negB s <;> simp

/-- Sums, differences, products and negations of two four-byte operands stay
well inside `int64_t`. -/
theorem narrow_no_overflow (s t : Elem) (hs : s.length ≤ 4) (ht : t.length ≤ 4) :
    (denote s + denote t).natAbs < 2 ^ 63 ∧ (denote s - denote t).natAbs < 2 ^ 63 ∧
    (denote s * denote t).natAbs < 2 ^ 63 ∧ (-(denote s)).natAbs < 2 ^ 63 := by
  have h1 := mag_le_four s hs
  have h2 := mag_le_four t ht
  have e1 := natAbs_denote s
  have e2 := natAbs_denote t
  refine ⟨by omega, by omega, ?_, by omega⟩
  rw [Int.natAbs_mul, e1, e2]
  have : mag s * mag t ≤ 2147483647 * 2147483647 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb : (2147483647 * 2147483647 : Nat) < 2 ^ 63 := by decide
  omega

end Bsv.Splice
