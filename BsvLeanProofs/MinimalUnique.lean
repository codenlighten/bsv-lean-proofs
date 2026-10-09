import BsvLeanProofs.Convert
import BsvLeanProofs.RoundTrip

/-!
# Minimal encodings are unique

Two minimally encoded byte strings that denote the same integer are the same
string. So `MinimallyEncode` computes THE canonical encoding of a value, and
OP_BIN2NUM after OP_NUM2BIN gives back the minimal encoding of the original
number.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

theorem natLE_lt (s : List Byte) : natLE s < 256 ^ s.length := by
  induction s with
  | nil => simp [natLE]
  | cons b s ih =>
    have hb := b.isLt
    simp only [natLE, List.length_cons, Nat.pow_succ]
    omega

theorem natLE_inj : ∀ (a b : List Byte), a.length = b.length → natLE a = natLE b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: a, y :: b, hl, hv => by
    have hx := x.isLt
    have hy := y.isLt
    simp only [natLE] at hv
    have h1 : x.toNat = y.toNat := by omega
    have h2 : natLE a = natLE b := by omega
    have hxy : x = y := BitVec.eq_of_toNat_eq h1
    rw [hxy, natLE_inj a b (by simpa using hl) h2]

set_option maxRecDepth 100000 in
theorem byte_split : ∀ l : Byte,
    l = (l &&& 0x7f#8) ||| (if l.msb then 0x80#8 else 0#8) := by
  apply forall_byte; decide

/-- A byte is determined by its low seven bits and its top bit. -/
theorem byte_ext (l l' : Byte) (h1 : l.toNat % 128 = l'.toNat % 128) (h2 : l.msb = l'.msb) :
    l = l' := by
  rw [toNat_mod128, toNat_mod128] at h1
  have h1' : l &&& 0x7f#8 = l' &&& 0x7f#8 := BitVec.eq_of_toNat_eq h1
  rw [byte_split l, byte_split l', h1', h2]

/-- Any string of `k + 1` bytes has magnitude below `128 · 256^k`. -/
theorem mag_snoc_lt (body : List Byte) (l : Byte) :
    mag (body ++ [l]) < 128 * 256 ^ body.length := by
  rw [mag_snoc]
  have h1 := natLE_lt body
  have h2 : l.toNat % 128 ≤ 127 := by omega
  have h3 : 256 ^ body.length * (l.toNat % 128) ≤ 256 ^ body.length * 127 :=
    Nat.mul_le_mul_left _ h2
  omega

theorem low7_pos (l : Byte) (h : ((l &&& 0x7f#8) != 0#8) = true) : 1 ≤ l.toNat % 128 := by
  rw [toNat_mod128]
  have hne : l &&& 0x7f#8 ≠ 0#8 := by simpa using h
  have : (l &&& 0x7f#8).toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  omega

set_option maxRecDepth 100000 in
theorem high_bit_ge (a : Byte) (h : ((a &&& 0x80#8) != 0#8) = true) : 128 ≤ a.toNat := by
  revert h
  revert a
  apply forall_byte
  decide

/-- A minimal string of one byte has magnitude at least 1. -/
theorem mag_single_ge (l : Byte) (h : isMinimal [l] = true) : 1 ≤ mag [l] := by
  have := low7_pos l (by simpa [isMinimal] using h)
  simpa [mag] using this

/-- A minimal string of `k + 2` bytes has magnitude at least `128 · 256^k`. -/
theorem mag_two_last_ge (pre : List Byte) (a l : Byte) (h : isMinimal (pre ++ [a, l]) = true) :
    128 * 256 ^ pre.length ≤ mag (pre ++ [a, l]) := by
  rw [isMinimal_two_last] at h
  have e : pre ++ [a, l] = (pre ++ [a]) ++ [l] := by simp
  rw [e, mag_snoc, natLE_append]
  simp only [natLE, List.length_append, List.length_cons, List.length_nil, Nat.mul_zero,
    Nat.add_zero, Nat.pow_succ]
  have hP : 0 < 256 ^ pre.length := Nat.pow_pos (by decide)
  rcases Bool.or_eq_true _ _ |>.mp h with hl | ha
  · have h1 := low7_pos l hl
    have h2 : 256 ^ pre.length * 256 * 1 ≤ 256 ^ pre.length * 256 * (l.toNat % 128) :=
      Nat.mul_le_mul_left _ h1
    omega
  · have h1 := high_bit_ge a ha
    have h2 : 256 ^ pre.length * 128 ≤ 256 ^ pre.length * a.toNat := Nat.mul_le_mul_left _ h1
    omega

/-- The magnitude of a minimal string determines its length: bounds that
depend on the length only and do not overlap. -/
def lowerBound : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => 128 * 256 ^ k

def upperBound : Nat → Nat
  | 0 => 1
  | k + 1 => 128 * 256 ^ k

theorem mag_lt_upper : ∀ s : List Byte, mag s < upperBound s.length := by
  intro s
  cases hr : s.reverse with
  | nil =>
    have : s = [] := by simpa using hr
    subst this; simp [mag, upperBound]
  | cons l rb =>
    have hs := eq_snoc_of_reverse hr
    have := mag_snoc_lt rb.reverse l
    rw [hs]
    simpa [upperBound] using this

theorem lower_le_mag (s : List Byte) (h : isMinimal s = true) : lowerBound s.length ≤ mag s := by
  cases hr : s.reverse with
  | nil =>
    have : s = [] := by simpa using hr
    subst this; simp [lowerBound]
  | cons l rb =>
    have hs := eq_snoc_of_reverse hr
    cases rb with
    | nil =>
      have hs' : s = [l] := by simpa using hs
      subst hs'
      simpa [lowerBound] using mag_single_ge l h
    | cons a rb' =>
      have hs' : s = rb'.reverse ++ [a, l] := by rw [hs]; simp
      subst hs'
      have := mag_two_last_ge rb'.reverse a l h
      simpa [lowerBound] using this

theorem upper_le_lower : ∀ (j k : Nat), j < k → upperBound j ≤ lowerBound k
  | 0, 1, _ => by simp [upperBound, lowerBound]
  | 0, k + 2, _ => by
    have : 0 < 256 ^ k := Nat.pow_pos (by decide)
    simp only [upperBound, lowerBound]; omega
  | j + 1, 1, h => by omega
  | j + 1, k + 2, h => by
    have : 256 ^ j ≤ 256 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [upperBound, lowerBound]; omega
  | _, 0, h => by omega

/-- Minimal strings with the same magnitude have the same length. -/
theorem length_eq_of_mag_eq (a b : List Byte) (ha : isMinimal a = true) (hb : isMinimal b = true)
    (h : mag a = mag b) : a.length = b.length := by
  have la := lower_le_mag a ha
  have ua := mag_lt_upper a
  have lb := lower_le_mag b hb
  have ub := mag_lt_upper b
  rcases Nat.lt_trichotomy a.length b.length with hlt | heq | hgt
  · have := upper_le_lower _ _ hlt; omega
  · exact heq
  · have := upper_le_lower _ _ hgt; omega

/-- Same length, same magnitude and same sign bit: the same string. -/
theorem eq_of_mag_negB (a b : List Byte) (hl : a.length = b.length) (hm : mag a = mag b)
    (hn : negB a = negB b) : a = b := by
  cases hra : a.reverse with
  | nil =>
    have ha : a = [] := by simpa using hra
    subst ha
    have : b.length = 0 := by simpa using hl.symm
    exact (List.length_eq_zero_iff.mp this).symm
  | cons la ra =>
    cases hrb : b.reverse with
    | nil =>
      have hb : b = [] := by simpa using hrb
      subst hb
      have : a.length = 0 := by simpa using hl
      exact List.length_eq_zero_iff.mp this
    | cons lb rb =>
      have hsa := eq_snoc_of_reverse hra
      have hsb := eq_snoc_of_reverse hrb
      subst hsa; subst hsb
      have hlen : ra.reverse.length = rb.reverse.length := by simpa using hl
      rw [mag_snoc, mag_snoc, hlen] at hm
      rw [negB_snoc, negB_snoc] at hn
      have h1 := natLE_lt ra.reverse
      have h2 := natLE_lt rb.reverse
      rw [hlen] at h1
      have hP : 0 < 256 ^ rb.reverse.length := Nat.pow_pos (by decide)
      -- divide by the common power
      have hq : la.toNat % 128 = lb.toNat % 128 := by
        have e1 : (natLE ra.reverse + 256 ^ rb.reverse.length * (la.toNat % 128)) /
            256 ^ rb.reverse.length = la.toNat % 128 := by
          rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h1, Nat.zero_add]
        have e2 : (natLE rb.reverse + 256 ^ rb.reverse.length * (lb.toNat % 128)) /
            256 ^ rb.reverse.length = lb.toNat % 128 := by
          rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h2, Nat.zero_add]
        rw [← e1, ← e2, hm]
      have hbody : natLE ra.reverse = natLE rb.reverse := by
        rw [hq] at hm; omega
      rw [natLE_inj _ _ hlen hbody, byte_ext la lb hq hn]

/-- **Uniqueness.** Two minimally encoded strings that denote the same integer
are equal. -/
theorem minimal_unique (a b : List Byte) (ha : isMinimal a = true) (hb : isMinimal b = true)
    (h : denote a = denote b) : a = b := by
  have hmag : mag a = mag b := by
    simp only [denote] at h
    cases hna : negB a <;> cases hnb : negB b <;> simp [hna, hnb] at h <;> omega
  have hlen := length_eq_of_mag_eq a b ha hb hmag
  by_cases h0 : mag a = 0
  · -- a minimal string of magnitude zero is empty
    have la := lower_le_mag a ha
    have lb := lower_le_mag b hb
    have ea : a.length = 0 := by
      match hk : a.length with
      | 0 => rfl
      | 1 => rw [hk] at la; simp [lowerBound] at la; omega
      | k + 2 =>
        rw [hk] at la
        have : 0 < 256 ^ k := Nat.pow_pos (by decide)
        simp [lowerBound] at la; omega
    have eb : b.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp ea, List.length_eq_zero_iff.mp eb]
  · have hsign : negB a = negB b := by
      simp only [denote] at h
      cases hna : negB a <;> cases hnb : negB b <;>
        simp only [hna, hnb, Bool.false_eq_true, ite_false, ite_true] at h <;>
        first | rfl | (exfalso; omega)
    exact eq_of_mag_negB a b hlen hmag hsign

/-- `MinimallyEncode` gives the one minimal string with the same value. -/
theorem minEnc_eq_of_minimal (s m : Elem) (hm : isMinimal m = true) (h : denote m = denote s) :
    minEnc s = m :=
  minimal_unique _ _ (isMinimal_minEnc s) hm (by rw [denote_minEnc, h])

/-- **OP_BIN2NUM after OP_NUM2BIN** gives the minimal encoding of the original
number, provided that encoding is not longer than `MaxScriptNumLength`. -/
theorem opBin2Num_opNum2Bin (p : Params) (top raw : Elem) (st r : Stack)
    (h : opNum2Bin p (top :: raw :: st) = .ok r) (hlen : (minEnc raw).length ≤ p.maxNumLen) :
    opBin2Num p r = .ok (minEnc raw :: st) := by
  obtain ⟨out, n, rfl, _, _, hden⟩ := opNum2Bin_ok p top raw st r h
  have e : minEnc out = minEnc raw :=
    minEnc_eq_of_minimal out (minEnc raw) (isMinimal_minEnc raw) (by rw [denote_minEnc, hden])
  simp [opBin2Num, e, isMinimalMax, hlen, isMinimal_minEnc]

/-- For a value that fits in `int64_t`, `MinimallyEncode` of any string
denoting it is what `bsv::serialize` produces for it. -/
theorem minEnc_eq_ser (s : Elem) (n : I64) (h : denote s = n.toInt) : minEnc s = ser n :=
  minEnc_eq_of_minimal s (ser n) (isMinimal_ser n)
    (by rw [h]; exact (deser123_toInt (ser n) n (deser123_ser n)).symm)

end Bsv.Splice
