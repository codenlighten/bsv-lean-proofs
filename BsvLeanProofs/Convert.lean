import BsvLeanProofs.MinEncode

/-!
# OP_NUM2BIN, OP_BIN2NUM and OP_SIZE

For the definitions in `Splice.lean`:
* OP_NUM2BIN, when it succeeds, leaves an element of exactly the requested
  length that denotes the same integer;
* OP_BIN2NUM, when it succeeds, leaves the minimal encoding of the same integer;
* OP_SIZE pushes a number that denotes the element's length.
Not proved here: that OP_BIN2NUM after OP_NUM2BIN gives back the minimal
encoding of the original number. It follows from uniqueness of minimal
encodings, which this file does not prove.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

set_option maxRecDepth 100000 in
theorem sign_byte_facts : ∀ l : Byte,
    (l &&& 0x80#8) &&& 0x7f#8 = 0#8 ∧ (l &&& 0x80#8).msb = l.msb := by
  apply forall_byte; decide

theorem sign_byte_low (l : Byte) : (l &&& 0x80#8).toNat % 128 = 0 := by
  rw [toNat_mod128, (sign_byte_facts l).1]; rfl

theorem sign_byte_msb (l : Byte) : (l &&& 0x80#8).msb = l.msb := (sign_byte_facts l).2

theorem natLE_replicate_zero (k : Nat) : natLE (List.replicate k (0#8)) = 0 :=
  natLE_zeros _ (fun x hx => (List.mem_replicate.mp hx).2)

/-- **OP_NUM2BIN.** On success the result has exactly the requested length and
denotes the same integer as the input. -/
theorem opNum2Bin_ok (p : Params) (top raw : Elem) (st r : Stack)
    (h : opNum2Bin p (top :: raw :: st) = .ok r) :
    ∃ out : Elem, ∃ n : Int, r = out :: st ∧
      scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top = .ok n ∧
      (out.length : Int) = n ∧ denote out = denote raw := by
  simp only [opNum2Bin] at h
  split at h
  · simp at h
  · rename_i n hn
    split at h
    · simp at h
    · rename_i hrange
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hrange
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i hgt
          have hden := denote_minEnc raw
          split at h
          · rename_i heq
            simp only [Except.ok.injEq] at h
            refine ⟨minEnc raw, n, h.symm, hn, ?_, hden⟩
            have : (minEnc raw).length = n.toNat := by simpa using heq
            omega
          · rename_i hne
            simp only [Except.ok.injEq] at h
            have hlt : (minEnc raw).length < n.toNat := by
              have h1 : ¬ (minEnc raw).length = n.toNat := by simpa using hne
              omega
            refine ⟨_, n, h.symm, hn, ?_, ?_⟩
            · -- length
              cases hr : (minEnc raw).reverse with
              | nil =>
                have hm : minEnc raw = [] := by simpa using hr
                simp only [hm, List.reverse_nil, List.length_nil] at hlt ⊢
                simp only [List.nil_append, List.length_append, List.length_replicate,
                  List.length_cons, List.length_nil]
                omega
              | cons l rb =>
                have hm := eq_snoc_of_reverse hr
                have hlen : (minEnc raw).length = rb.length + 1 := by rw [hm]; simp
                simp only [List.length_append, List.length_reverse, List.length_cons,
                  List.length_replicate, List.length_nil]
                omega
            · -- value
              rw [← hden]
              cases hr : (minEnc raw).reverse with
              | nil =>
                have hm : minEnc raw = [] := by simpa using hr
                simp only [hm, List.getLast?_nil, List.nil_append]
                rw [denote_snoc, natLE_replicate_zero]
                simp
                rfl
              | cons l rb =>
                have hm := eq_snoc_of_reverse hr
                have hlast : (minEnc raw).getLast? = some l := by rw [hm]; simp
                simp only [hlast]
                rw [hm, denote_snoc, denote_snoc, sign_byte_msb, sign_byte_low]
                have e1 : natLE (((l &&& 0x7f#8) :: rb).reverse ++
                    List.replicate (n.toNat - (rb.reverse ++ [l]).length - 1) 0#8) =
                    natLE rb.reverse + 256 ^ rb.reverse.length * (l.toNat % 128) := by
                  rw [natLE_append, natLE_replicate_zero, List.reverse_cons, natLE_append,
                    toNat_mod128]
                  simp [natLE]
                rw [e1]
                simp

/-- **OP_BIN2NUM.** On success the result is the minimal encoding of the same
integer, no longer than `MaxScriptNumLength`. -/
theorem opBin2Num_ok (p : Params) (x : Elem) (st r : Stack)
    (h : opBin2Num p (x :: st) = .ok r) :
    r = minEnc x :: st ∧ isMinimal (minEnc x) = true ∧ (minEnc x).length ≤ p.maxNumLen ∧
      denote (minEnc x) = denote x := by
  simp only [opBin2Num] at h
  split at h
  · simp at h
  · rename_i hmin
    simp only [Except.ok.injEq] at h
    have hm : isMinimalMax (minEnc x) p.maxNumLen = true := by simpa using hmin
    simp only [isMinimalMax, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨h.symm, hm.2, hm.1, denote_minEnc x⟩

/-- OP_BIN2NUM fails only for length: the minimal encoding is too long. -/
theorem opBin2Num_error (p : Params) (x : Elem) (st : Stack) (e : Err)
    (h : opBin2Num p (x :: st) = .error e) :
    e = .invalidNumberRange ∧ p.maxNumLen < (minEnc x).length := by
  simp only [opBin2Num] at h
  split at h
  · rename_i hmin
    simp only [Except.error.injEq] at h
    refine ⟨h.symm, ?_⟩
    have := isMinimal_minEnc x
    simp only [isMinimalMax, this, Bool.and_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_le] at hmin
    exact hmin
  · simp at h

/-! ## OP_SIZE -/

theorem negB_cons (b : Byte) (t : List Byte) (ht : t ≠ []) : negB (b :: t) = negB t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons c bs => simp [negB]

theorem mag_cons (b : Byte) (t : List Byte) (ht : t ≠ []) : mag (b :: t) = b.toNat + 256 * mag t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons c bs => rw [mag]

/-- The encoding of a length denotes that length, and is not negative. -/
theorem encNatLoop_spec : ∀ (fuel n : Nat), n < fuel →
    mag (encNatLoop fuel n) = n ∧ negB (encNatLoop fuel n) = false ∧
      (n ≠ 0 → encNatLoop fuel n ≠ [])
  | 0, n, h => by omega
  | fuel + 1, n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [encNatLoop, mag, negB]
    · by_cases h1 : n < 128
      · have hmod : n % 256 = n := Nat.mod_eq_of_lt (by omega)
        have hmsb : (BitVec.ofNat 8 n).msb = false := by
          rw [BitVec.msb_eq_decide]; simp [hmod]; omega
        simp [encNatLoop, h0, h1, mag, negB, hmod, hmsb]
      · by_cases h2 : n < 256
        · have hmod : n % 256 = n := Nat.mod_eq_of_lt h2
          simp [encNatLoop, h0, h1, h2, mag, negB, hmod]
        · obtain ⟨i1, i2, i3⟩ := encNatLoop_spec fuel (n / 256) (by omega)
          have hne := i3 (by omega)
          simp only [encNatLoop, h0, h1, h2, beq_iff_eq, ite_false]
          refine ⟨?_, ?_, by simp⟩
          · rw [mag_cons _ _ hne, i1]; simp; omega
          · rw [negB_cons _ _ hne, i2]

theorem denote_encNat (n : Nat) : denote (encNat n) = n := by
  obtain ⟨h1, h2, _⟩ := encNatLoop_spec (n + 1) n (by omega)
  simp [denote, encNat, h1, h2]

/-- **OP_SIZE.** On success the element is kept and a number denoting its
length is pushed on top of it. -/
theorem opSize_ok (p : Params) (x : Elem) (st r : Stack) (h : opSize p (x :: st) = .ok r) :
    ∃ e : Elem, r = e :: x :: st ∧ denote e = x.length := by
  simp only [opSize] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h
    exact ⟨encNat x.length, h.symm, denote_encNat x.length⟩

end Bsv.Splice
