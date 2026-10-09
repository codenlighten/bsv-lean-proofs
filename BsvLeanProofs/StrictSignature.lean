/-!
# The block-signature parser accepts one encoding of each (r, s)

A model of `strict_signature` and `strict_integer` in an
independent, unpublished Rust node implementation (its
`node/crates/chain/src/signing.rs` at commit 771670a), not bitcoin-sv.

What is modelled: the two parsers up to the pair of 32-byte big-endian values
`(r, s)` they hand to the signature library.
What is proved: every accepted byte string is the canonical encoding of the
pair it yields, so two accepted strings with the same pair are equal.
What is not modelled: `Signature::from_components` and the low-S test. The
result carries over to the full parser only if those two refuse or accept a
pair without merging two different pairs into one signature. In the source
`from_components` calls `Scalar::from_be_bytes_checked` on each value and
refuses zero, and `from_be_bytes_checked` (`scalar.rs`) returns a value only
when it is below the curve order, never a reduced one. So the assumption holds
on a reading of those few lines of Rust, which are not modelled here.
The theorem says at most one accepted string per pair. It says nothing about
whether two different pairs can both be valid signatures of one block.
-/

namespace Bsv.StrictSignature

abbrev Byte := BitVec 8

/-- "Padded with a zero the next byte does not need". -/
def padded (v0 : Byte) : List Byte → Bool
  | [] => false
  | v1 :: _ => v0 == 0#8 && !v1.msb

/-- `strict_integer`: the 32-byte value and the unread remainder. -/
def strictInt : List Byte → Option (List Byte × List Byte)
  | tag :: len :: rest =>
    let n := len.toNat
    if tag != 0x02#8 || n == 0 || decide (n > 33) || decide (rest.length < n) then none else
    match rest.take n with
    | [] => none
    | v0 :: vt =>
      -- negative, or padded
      if v0.msb || padded v0 vt then none else
      -- thirty-three bytes only with a leading zero
      if vt.length == 32 && v0 != 0#8 then none else
      let value := if vt.length == 32 then vt else v0 :: vt
      some (List.replicate (32 - value.length) 0#8 ++ value, rest.drop n)
  | _ => none

/-- `strict_signature`, up to the pair `(r, s)`. -/
def strictSig : List Byte → Option (List Byte × List Byte)
  | seq :: len :: body =>
    if seq != 0x30#8 || len.toNat != body.length then none else
    match strictInt body with
    | none => none
    | some (r, body) =>
      match strictInt body with
      | none => none
      | some (s, body) => if body.isEmpty then some (r, s) else none
  | _ => none

/-- The canonical content bytes for a big-endian value: leading zeros removed,
one zero byte kept for zero or put back when the top bit is set. -/
def canon (out : List Byte) : List Byte :=
  match out.dropWhile (· == 0#8) with
  | [] => [0#8]
  | h :: t => if h.msb then 0#8 :: h :: t else h :: t

/-- The canonical DER INTEGER. -/
def encInt (out : List Byte) : List Byte :=
  0x02#8 :: BitVec.ofNat 8 (canon out).length :: canon out

def encSig (r s : List Byte) : List Byte :=
  0x30#8 :: BitVec.ofNat 8 (encInt r ++ encInt s).length :: (encInt r ++ encInt s)

theorem dropWhile_replicate_zero (k : Nat) (l : List Byte) :
    (List.replicate k 0#8 ++ l).dropWhile (· == 0#8) = l.dropWhile (· == 0#8) := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.dropWhile_cons, ih]

theorem msb_ne_zero (b : Byte) (h : b.msb = true) : (b == 0#8) = false := by
  cases hb : (b == 0#8)
  · rfl
  · have : b = 0#8 := by simpa using hb
    subst this
    simp at h

/-- The content bytes the parser accepts are the canonical ones for the value
it returns. -/
theorem canon_value (v0 : Byte) (vt : List Byte)
    (hneg : v0.msb = false) (hpad : padded v0 vt = false)
    (h33 : (vt.length == 32 && v0 != 0#8) = false) :
    canon (List.replicate (32 - (if vt.length == 32 then vt else v0 :: vt).length) 0#8 ++
      (if vt.length == 32 then vt else v0 :: vt)) = v0 :: vt := by
  unfold canon
  rw [dropWhile_replicate_zero]
  cases vt with
  | nil =>
    by_cases h0 : v0 = 0#8
    · subst h0; simp [List.dropWhile_cons]
    · simp [List.dropWhile_cons, h0, hneg]
  | cons v1 u =>
    by_cases h0 : v0 = 0#8
    · subst h0
      have hm : v1.msb = true := by simpa [padded] using hpad
      have hz := msb_ne_zero v1 hm
      have hz' : ¬ v1 = 0#8 := by simpa using hz
      by_cases hl : u.length = 31
      · simp [hl, List.dropWhile_cons, hz', hm]
      · simp [hl, List.dropWhile_cons, hz', hm]
    · have hl : ¬ u.length = 31 := by
        intro hl; simp [hl, h0] at h33
      simp [hl, List.dropWhile_cons, h0, hneg]

/-- An accepted INTEGER is the canonical encoding of its value, followed by
the unread remainder. -/
theorem strictInt_eq (b out rest : List Byte) (h : strictInt b = some (out, rest)) :
    b = encInt out ++ rest := by
  match b, h with
  | [], h => simp [strictInt] at h
  | [_], h => simp [strictInt] at h
  | tag :: len :: tl, h =>
    simp only [strictInt] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq, not_or,
        Decidable.not_not, Nat.not_lt] at hc
      obtain ⟨⟨⟨htag, _⟩, _⟩, hlen⟩ := hc
      have htake : (tl.take len.toNat).length = len.toNat := by
        simp only [List.length_take]; omega
      have hsplit : tl = tl.take len.toNat ++ tl.drop len.toNat :=
        (List.take_append_drop _ _).symm
      generalize tl.take len.toNat = v at h htake hsplit
      match v, h with
      | [], h => simp at h
      | v0 :: vt, h =>
        simp only at h
        split at h
        · simp at h
        · rename_i hneg
          split at h
          · simp at h
          · rename_i h33
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hout, hrest⟩ := h
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hneg
            have hcanon := canon_value v0 vt hneg.1 hneg.2 (by simpa using h33)
            rw [hout] at hcanon
            have hlenb : len = BitVec.ofNat 8 (v0 :: vt).length := by
              rw [htake]; simp
            rw [encInt, hcanon, ← hlenb, htag, hsplit, hrest]
            simp

/-- **An accepted signature is the canonical encoding of the pair it yields.** -/
theorem strictSig_eq (b r s : List Byte) (h : strictSig b = some (r, s)) :
    b = encSig r s := by
  match b, h with
  | [], h => simp [strictSig] at h
  | [_], h => simp [strictSig] at h
  | seq :: len :: body, h =>
    simp only [strictSig] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
      obtain ⟨hseq, hlen⟩ := hc
      split at h
      · simp at h
      · rename_i r' body1 hr
        split at h
        · simp at h
        · rename_i s' body2 hs
          split at h
          · rename_i hemp
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have e1 := strictInt_eq _ _ _ hr
            have e2 := strictInt_eq _ _ _ hs
            have hb2 : body2 = [] := by simpa using hemp
            subst hb2
            have hbody : body = encInt r' ++ encInt s' := by rw [e1, e2]; simp
            have hlenb : len = BitVec.ofNat 8 body.length := by rw [← hlen]; simp
            rw [encSig, ← hbody, ← hlenb, hseq]
          · simp at h

/-- **Uniqueness.** Two accepted byte strings that yield the same `(r, s)` are
the same byte string. -/
theorem strictSig_injective (b₁ b₂ r s : List Byte)
    (h₁ : strictSig b₁ = some (r, s)) (h₂ : strictSig b₂ = some (r, s)) : b₁ = b₂ := by
  rw [strictSig_eq _ _ _ h₁, strictSig_eq _ _ _ h₂]

/-! ## Examples: the parser does accept, and refuses the known bad shapes -/

/-- r = 1, s = 1 is accepted. -/
example : (strictSig [0x30, 6, 2, 1, 1, 2, 1, 1]).isSome = true := by decide

/-- A zero-padded 1 is refused. -/
example : strictInt [2, 2, 0, 1] = none := by decide

/-- A negative INTEGER is refused. -/
example : strictInt [2, 1, 0x80] = none := by decide

/-- 0x80 with the zero it needs is accepted. -/
example : (strictInt [2, 2, 0, 0x80]).isSome = true := by decide

/-- Thirty-three bytes whose first byte is not zero are refused (the case an
earlier version truncated). -/
example : strictInt (2 :: 33 :: 1 :: List.replicate 32 0xff) = none := by decide

/-- Trailing bytes are refused. -/
example : strictSig [0x30, 6, 2, 1, 1, 2, 1, 1, 0] = none := by decide

end Bsv.StrictSignature
