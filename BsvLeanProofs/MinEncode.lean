import BsvLeanProofs.Splice

/-!
# `MinimallyEncode` is correct

For the model `minEnc` of `bsv::MinimallyEncode` (`Splice.lean`):
* it does not change the integer the bytes denote;
* its result is minimally encoded;
* it leaves a minimally encoded string unchanged.
These hold for strings of any length, so they cover the big-integer numbers
used after Genesis as well as the narrow ones.
Facts about single bytes are proved by checking all 256 values in the kernel.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-! ## Little-endian values of byte strings -/

/-- The plain little-endian value: every byte counts in full. -/
def natLE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * natLE bs

theorem natLE_append (a b : List Byte) :
    natLE (a ++ b) = natLE a + 256 ^ a.length * natLE b := by
  induction a with
  | nil => simp [natLE]
  | cons x a ih =>
    have e : 256 ^ (a.length + 1) * natLE b = 256 * (256 ^ a.length * natLE b) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ a.length) 256, Nat.mul_assoc]
    simp only [List.cons_append, natLE, ih, List.length_cons, e]
    omega

theorem natLE_zeros (z : List Byte) (h : ∀ x ∈ z, x = 0#8) : natLE z = 0 := by
  induction z with
  | nil => rfl
  | cons x z ih =>
    have hx := h x (by simp)
    subst hx
    simp [natLE, ih (fun y hy => h y (by simp [hy]))]

theorem mag_snoc (body : List Byte) (l : Byte) :
    mag (body ++ [l]) = natLE body + 256 ^ body.length * (l.toNat % 128) := by
  induction body with
  | nil => simp [mag, natLE]
  | cons b body ih =>
    cases body with
    | nil => simp [mag, natLE]
    | cons c bs =>
      have e : 256 ^ ((c :: bs).length + 1) * (l.toNat % 128) =
          256 * (256 ^ (c :: bs).length * (l.toNat % 128)) := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ (c :: bs).length) 256, Nat.mul_assoc]
      have ih' : mag (c :: (bs ++ [l])) =
          natLE (c :: bs) + 256 ^ (c :: bs).length * (l.toNat % 128) := ih
      show mag (b :: c :: (bs ++ [l])) = _
      rw [mag, ih']
      simp only [natLE, List.length_cons] at e ⊢
      omega

theorem negB_snoc (body : List Byte) (l : Byte) : negB (body ++ [l]) = l.msb := by
  simp [negB]

theorem denote_snoc (body : List Byte) (l : Byte) :
    denote (body ++ [l]) =
      if l.msb then -((natLE body + 256 ^ body.length * (l.toNat % 128) : Nat) : Int)
      else ((natLE body + 256 ^ body.length * (l.toNat % 128) : Nat) : Int) := by
  simp only [denote, negB_snoc, mag_snoc]

/-! ## Facts about single bytes -/

theorem toNat_mod128 (x : Byte) : x.toNat % 128 = (x &&& 0x7f#8).toNat := by
  rw [BitVec.toNat_and]
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 7).symm

theorem low7_zero (l : Byte) (h : ((l &&& 0x7f#8) != 0#8) = false) : l.toNat % 128 = 0 := by
  rw [toNat_mod128]
  have : l &&& 0x7f#8 = 0#8 := by simpa using h
  rw [this]; rfl

/-- A statement about every byte follows from checking the 256 values. -/
theorem forall_byte {P : Byte → Prop} (h : ∀ n : Fin 256, P (BitVec.ofFin n)) : ∀ b : Byte, P b :=
  fun b => h b.toFin

set_option maxRecDepth 100000 in
theorem sign_byte_cases : ∀ l : Byte, ((l &&& 0x7f#8) != 0#8) = false → l = 0#8 ∨ l = 0x80#8 := by
  apply forall_byte; decide

set_option maxRecDepth 100000 in
theorem low_byte_facts : ∀ b : Byte, ((b &&& 0x80#8) != 0#8) = false →
    b &&& 0x7f#8 = b ∧ (b ||| 0x80#8) &&& 0x7f#8 = b ∧ b.msb = false := by
  apply forall_byte; decide

theorem or_sign_low (b l : Byte) (hb : ((b &&& 0x80#8) != 0#8) = false)
    (hl : ((l &&& 0x7f#8) != 0#8) = false) : (b ||| l) &&& 0x7f#8 = b := by
  obtain ⟨h1, h2, _⟩ := low_byte_facts b hb
  rcases sign_byte_cases l hl with rfl | rfl
  · simpa using h1
  · exact h2

theorem or_sign_msb (b l : Byte) (hb : ((b &&& 0x80#8) != 0#8) = false) :
    (b ||| l).msb = l.msb := by
  obtain ⟨_, _, h3⟩ := low_byte_facts b hb
  rw [BitVec.msb_or, h3, Bool.false_or]

theorem or_sign_toNat (b l : Byte) (hb : ((b &&& 0x80#8) != 0#8) = false)
    (hl : ((l &&& 0x7f#8) != 0#8) = false) : (b ||| l).toNat % 128 = b.toNat := by
  rw [toNat_mod128, or_sign_low b l hb hl]

/-! ## The loop -/

theorem dw_pos (x : Byte) (rb : List Byte) (h : (x == 0#8) = true) :
    (x :: rb).dropWhile (· == 0#8) = rb.dropWhile (· == 0#8) := by
  simp [List.dropWhile_cons, h]

theorem dw_neg (x : Byte) (rb : List Byte) (h : ¬ (x == 0#8) = true) :
    (x :: rb).dropWhile (· == 0#8) = x :: rb := by
  simp [List.dropWhile_cons, h]

/-- The loop skips the zero bytes and then acts on the first non-zero one. -/
theorem trim_eq (l : Byte) : ∀ rb : List Byte,
    trim l rb = match rb.dropWhile (· == 0#8) with
      | [] => []
      | b :: bs => if (b &&& 0x80#8) != 0#8 then l :: b :: bs else (b ||| l) :: bs
  | [] => rfl
  | b :: bs => by
    by_cases hb : (b == 0#8) = true
    · rw [dw_pos b bs hb]
      simp only [trim, hb, ite_true]
      exact trim_eq l bs
    · rw [dw_neg b bs hb]
      simp only [trim, hb, Bool.false_eq_true, ite_false]

theorem dropWhile_head_ne (rb : List Byte) (b : Byte) (bs : List Byte)
    (h : rb.dropWhile (· == 0#8) = b :: bs) : (b == 0#8) = false := by
  induction rb with
  | nil => simp at h
  | cons x rb ih =>
    by_cases hx : (x == 0#8) = true
    · rw [dw_pos x rb hx] at h; exact ih h
    · rw [dw_neg x rb hx] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]; simpa using hx

/-- Dropping the zero bytes from the top does not change the value. -/
theorem natLE_reverse_dropWhile (rb : List Byte) :
    natLE (rb.dropWhile (· == 0#8)).reverse = natLE rb.reverse := by
  induction rb with
  | nil => rfl
  | cons x rb ih =>
    by_cases hx : (x == 0#8) = true
    · have hx0 : x = 0#8 := by simpa using hx
      rw [dw_pos x rb hx, ih, List.reverse_cons, natLE_append]
      subst hx0
      simp [natLE]
    · rw [dw_neg x rb hx]

/-! ## Minimality in terms of the last two bytes -/

theorem isMinimal_cons (x : Byte) : ∀ t : List Byte, 2 ≤ t.length →
    isMinimal (x :: t) = isMinimal t
  | [], h => by simp at h
  | [_], h => by simp at h
  | _ :: _ :: _, _ => by rw [isMinimal]

theorem isMinimal_two_last (pre : List Byte) (a l : Byte) :
    isMinimal (pre ++ [a, l]) = ((l &&& 0x7f#8) != 0#8 || (a &&& 0x80#8) != 0#8) := by
  induction pre with
  | nil => rfl
  | cons x pre ih =>
    show isMinimal (x :: (pre ++ [a, l])) = _
    rw [isMinimal_cons x _ (by simp), ih]

theorem eq_snoc_of_reverse {s : List Byte} {l : Byte} {rb : List Byte}
    (h : s.reverse = l :: rb) : s = rb.reverse ++ [l] := by
  have := congrArg List.reverse h
  simpa using this

/-! ## The three theorems -/

/-- A minimally encoded string is left unchanged. -/
theorem minEnc_of_isMinimal (s : Elem) (h : isMinimal s = true) : minEnc s = s := by
  unfold minEnc
  cases hr : s.reverse with
  | nil =>
    have : s = [] := by simpa using hr
    subst this; rfl
  | cons l rb =>
    have hs := eq_snoc_of_reverse hr
    by_cases hl : ((l &&& 0x7f#8) != 0#8) = true
    · simp only [minEncRev, hl, if_true]
      rw [← hr, List.reverse_reverse]
    · have hl' : ((l &&& 0x7f#8) != 0#8) = false := by simpa using hl
      cases rb with
      | nil =>
        subst hs
        simp [isMinimal, hl'] at h
      | cons a rb' =>
        by_cases ha : ((a &&& 0x80#8) != 0#8) = true
        · simp only [minEncRev, hl, Bool.false_eq_true, if_false, ha, if_true]
          rw [← hr, List.reverse_reverse]
        · have ha' : ((a &&& 0x80#8) != 0#8) = false := by simpa using ha
          have hs' : s = rb'.reverse ++ [a, l] := by rw [hs]; simp
          rw [hs', isMinimal_two_last, hl', ha'] at h
          simp at h

/-- The result of `MinimallyEncode` is minimally encoded. -/
theorem isMinimal_minEnc (s : Elem) : isMinimal (minEnc s) = true := by
  unfold minEnc
  cases hr : s.reverse with
  | nil => rfl
  | cons l rb =>
    have hs := eq_snoc_of_reverse hr
    by_cases hl : ((l &&& 0x7f#8) != 0#8) = true
    · simp only [minEncRev, hl, if_true]
      cases rb with
      | nil => simp [isMinimal, hl]
      | cons a rb' =>
        have : (l :: a :: rb').reverse = rb'.reverse ++ [a, l] := by simp
        rw [this, isMinimal_two_last, hl]; rfl
    · have hl' : ((l &&& 0x7f#8) != 0#8) = false := by simpa using hl
      cases rb with
      | nil => simp [minEncRev, hl']; rfl
      | cons a rb' =>
        by_cases ha : ((a &&& 0x80#8) != 0#8) = true
        · simp only [minEncRev, hl, Bool.false_eq_true, if_false, ha, if_true]
          have : (l :: a :: rb').reverse = rb'.reverse ++ [a, l] := by simp
          rw [this, isMinimal_two_last, ha]; simp
        · simp only [minEncRev, hl, Bool.false_eq_true, if_false, ha, trim_eq]
          cases hd : (a :: rb').dropWhile (· == 0#8) with
          | nil => rfl
          | cons b bs =>
            have hb0 := dropWhile_head_ne _ b bs hd
            by_cases hb : ((b &&& 0x80#8) != 0#8) = true
            · simp only [hb, if_true]
              have : (l :: b :: bs).reverse = bs.reverse ++ [b, l] := by simp
              rw [this, isMinimal_two_last, hb]; simp
            · have hb' : ((b &&& 0x80#8) != 0#8) = false := by simpa using hb
              have hlow := or_sign_low b l hb' hl'
              have hne : (((b ||| l) &&& 0x7f#8) != 0#8) = true := by
                rw [hlow]; simpa using hb0
              simp only [hb, Bool.false_eq_true, if_false]
              cases bs with
              | nil => simp [isMinimal, hne]
              | cons c bs' =>
                have : ((b ||| l) :: c :: bs').reverse = bs'.reverse ++ [c, b ||| l] := by simp
                rw [this, isMinimal_two_last, hne]; rfl

/-- `MinimallyEncode` does not change the integer the bytes denote. -/
theorem denote_minEnc (s : Elem) : denote (minEnc s) = denote s := by
  unfold minEnc
  cases hr : s.reverse with
  | nil =>
    have : s = [] := by simpa using hr
    subst this; rfl
  | cons l rb =>
    have hs := eq_snoc_of_reverse hr
    by_cases hl : ((l &&& 0x7f#8) != 0#8) = true
    · simp only [minEncRev, hl, if_true]
      rw [← hr, List.reverse_reverse]
    · have hl' : ((l &&& 0x7f#8) != 0#8) = false := by simpa using hl
      have hl0 := low7_zero l hl'
      have hden : denote s = if l.msb then -((natLE rb.reverse : Nat) : Int)
          else ((natLE rb.reverse : Nat) : Int) := by
        rw [hs, denote_snoc, hl0]; simp
      have hzero : denote ([] : Elem) = 0 := rfl
      cases rb with
      | nil =>
        simp only [minEncRev, hl, Bool.false_eq_true, if_false]
        rw [hden]; simp [natLE]; exact hzero
      | cons a rb' =>
        by_cases ha : ((a &&& 0x80#8) != 0#8) = true
        · simp only [minEncRev, hl, Bool.false_eq_true, if_false, ha, if_true]
          rw [← hr, List.reverse_reverse]
        · simp only [minEncRev, hl, Bool.false_eq_true, if_false, ha, trim_eq]
          have hval := natLE_reverse_dropWhile (a :: rb')
          cases hd : (a :: rb').dropWhile (· == 0#8) with
          | nil =>
            rw [hd] at hval
            simp only [List.reverse_nil, natLE] at hval
            rw [hden, ← hval]; simp; exact hzero
          | cons b bs =>
            rw [hd] at hval
            by_cases hb : ((b &&& 0x80#8) != 0#8) = true
            · simp only [hb, if_true]
              have e : (l :: b :: bs).reverse = (b :: bs).reverse ++ [l] := by simp
              rw [e, denote_snoc, hl0, hden, ← hval]; simp
            · have hb' : ((b &&& 0x80#8) != 0#8) = false := by simpa using hb
              simp only [hb, Bool.false_eq_true, if_false]
              have e : ((b ||| l) :: bs).reverse = bs.reverse ++ [b ||| l] := by simp
              have hv : natLE (b :: bs).reverse = natLE bs.reverse + 256 ^ bs.length * b.toNat := by
                rw [List.reverse_cons, natLE_append]; simp [natLE]
              rw [e, denote_snoc, or_sign_msb b l hb', or_sign_toNat b l hb' hl', hden, ← hval, hv]
              simp

end Bsv.Splice
