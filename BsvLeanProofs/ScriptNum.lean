import Std.Tactic.BVDecide

/-!
# The narrow script-number reader of bitcoin-sv, versions 1.2.2 and 1.2.3

A model of `bsv::deserialize<int64_t>` (`src/script/int_serialization.h`) at tags
v1.2.2 and v1.2.3, and a proof of exactly which byte strings 1.2.3 accepts.

What is modelled: the body of the function, statement by statement, on
`BitVec 64` (two's complement, as C++20 specifies for `int64_t`).
What is assumed:
* C++20 semantics for `<<` on signed integers (the result is the wrapped value;
  the shift counts here are never negative, so a count of 64 or more is the
  only way a shift can be undefined);
* for 1.2.2 on operands longer than nine bytes, where the source is undefined,
  the shift count is taken modulo 64, as the x86 scalar `shl` instruction does.
  That describes one compiled behaviour, not the source. Support: the test in
  `Fixtures.lean`, and (reported by an independent review, not checked
  here) a disassembly of GoBDK's x86_64 library showing scalar `shl`.
Nothing here models the callers (`CScriptNum`, the interpreter).

Tested against the source (`difftest/run.sh`, a test and not a proof): drivers
compiled from the unmodified headers agree with these models on every input
tried, with the sanitizers reporting nothing for 1.2.3.
-/

namespace Bsv.ScriptNum

abbrev Byte := BitVec 8
abbrev I64 := BitVec 64

def intMin : I64 := 0x8000000000000000#64

/-! ## The mathematical meaning of a byte string -/

/-- Magnitude of a little-endian sign-magnitude string: every byte counts in
full except the last, whose top bit is the sign. -/
def mag : List Byte → Nat
  | [] => 0
  | [b] => b.toNat % 128
  | b :: c :: bs => b.toNat + 256 * mag (c :: bs)

/-- The sign bit: the top bit of the last byte. -/
def negB (s : List Byte) : Bool := (s.getLastD 0).msb

/-- The integer a byte string denotes. Negative zero denotes 0. -/
def denote (s : List Byte) : Int := if negB s then -(mag s : Int) else (mag s : Int)

/-! ## 1.2.3 -/

/-- The loop `for i < d - 1: result |= int64(s[i]) << 8*i`. The last byte is
not read. -/
def foldLow : List Byte → Nat → I64 → I64
  | [], _, acc => acc
  | [_], _, acc => acc
  | b :: c :: bs, i, acc => foldLow (c :: bs) (i + 1) (acc ||| (b.setWidth 64 <<< (8 * i)))

/-- `bsv::deserialize<int64_t>` at v1.2.3. `none` is `std::nullopt`. -/
def deser123 (s : List Byte) : Option I64 :=
  match s with
  | [] => some 0
  | _ =>
    let d := s.length
    if d > 9 then none else
    let last := s.getLastD 0
    if d == 9 && (last &&& 0x7f#8) != 0 then none else
    let result := foldLow s 0 0
    let tmp : I64 := last.setWidth 64
    let negative := (tmp &&& 0x80#64) != 0
    if d ≤ 8 then
      let tmp := if negative then tmp &&& 0x7f#64 else tmp
      let result := result ||| (tmp <<< (8 * (d - 1)))
      some (if negative then -result else result)
    else
      if result == intMin then (if negative then some result else none)
      else if result.slt 0 then none
      else some (if negative then -result else result)

/-! ### The same function with the undefined operations checked

The outer `none` means "an operation with undefined behaviour was reached":
a shift by 64 or more, or the negation of `INT64_MIN`. -/

def shl? (x : I64) (k : Nat) : Option I64 := if k < 64 then some (x <<< k) else none
def neg? (x : I64) : Option I64 := if x == intMin then none else some (-x)

def foldLow? : List Byte → Nat → I64 → Option I64
  | [], _, acc => some acc
  | [_], _, acc => some acc
  | b :: c :: bs, i, acc =>
    match shl? (b.setWidth 64) (8 * i) with
    | none => none
    | some t => foldLow? (c :: bs) (i + 1) (acc ||| t)

def deser123? (s : List Byte) : Option (Option I64) :=
  match s with
  | [] => some (some 0)
  | _ =>
    let d := s.length
    if d > 9 then some none else
    let last := s.getLastD 0
    if d == 9 && (last &&& 0x7f#8) != 0 then some none else
    match foldLow? s 0 0 with
    | none => none
    | some result =>
      let tmp : I64 := last.setWidth 64
      let negative := (tmp &&& 0x80#64) != 0
      if d ≤ 8 then
        let tmp := if negative then tmp &&& 0x7f#64 else tmp
        match shl? tmp (8 * (d - 1)) with
        | none => none
        | some t =>
          let result := result ||| t
          if negative then (neg? result).map some else some (some result)
      else
        if result == intMin then some (if negative then some result else none)
        else if result.slt 0 then some none
        else if negative then (neg? result).map some else some (some result)

/-! ## 1.2.2, as the x86 scalar build runs it -/

/-- The 1.2.2 loop with the shift count taken modulo 64 (x86 `shl`). For
`i < 8` this is the defined C++ meaning; beyond that the source is undefined. -/
def foldLowX86 : List Byte → Nat → I64 → I64
  | [], _, acc => acc
  | [_], _, acc => acc
  | b :: c :: bs, i, acc =>
    foldLowX86 (c :: bs) (i + 1) (acc ||| (b.setWidth 64 <<< (8 * i % 64)))

/-- `bsv::deserialize<int64_t>` at v1.2.2. The source requires a non-empty
range; on `[]` this model returns 0 only so that it is total. -/
def deser122 (s : List Byte) : I64 :=
  let d := s.length
  let result := foldLowX86 s 0 0
  if d > 8 then result else
  let tmp : I64 := (s.getLastD 0).setWidth 64
  let negative := (tmp &&& 0x80#64) != 0
  let tmp := if negative then tmp &&& 0x7f#64 else tmp
  let result := result ||| (tmp <<< (8 * (d - 1)))
  if negative then -result else result

/-! ## The specification, in bit-vector form (a stepping stone) -/

def magBV : List Byte → BitVec 72
  | [] => 0
  | [b] => (b.setWidth 7).setWidth 72
  | b :: c :: bs => b.setWidth 72 + (magBV (c :: bs) <<< 8)

def fitsBV (s : List Byte) : Bool :=
  (negB s && (magBV s).ule 0x8000000000000000#72) ||
  (!negB s && (magBV s).ult 0x8000000000000000#72)

def specBV (s : List Byte) : Option I64 :=
  if s.length ≤ 9 ∧ fitsBV s = true
  then some ((if negB s then -magBV s else magBV s).setWidth 64) else none

/-! ## Proof tools -/

theorem opt_eq {a b : Option I64} (h1 : a.isSome = b.isSome) (h2 : a.getD 0 = b.getD 0) :
    a = b := by
  cases a <;> cases b <;> simp_all

@[simp] theorem isSome_ite' {α} (c : Prop) [Decidable c] (a b : Option α) :
    (if c then a else b).isSome = if c then a.isSome else b.isSome := by split <;> rfl
@[simp] theorem getD_ite' {α} (c : Prop) [Decidable c] (a b : Option α) (d : α) :
    (if c then a else b).getD d = if c then a.getD d else b.getD d := by split <;> rfl

/-- Every list of length at most nine is one of ten explicit shapes. -/
theorem forall_len_le9 {P : List Byte → Prop}
    (h0 : P [])
    (h1 : ∀ a, P [a])
    (h2 : ∀ a b, P [a, b])
    (h3 : ∀ a b c, P [a, b, c])
    (h4 : ∀ a b c d, P [a, b, c, d])
    (h5 : ∀ a b c d e, P [a, b, c, d, e])
    (h6 : ∀ a b c d e f, P [a, b, c, d, e, f])
    (h7 : ∀ a b c d e f g, P [a, b, c, d, e, f, g])
    (h8 : ∀ a b c d e f g h, P [a, b, c, d, e, f, g, h])
    (h9 : ∀ a b c d e f g h i, P [a, b, c, d, e, f, g, h, i]) :
    ∀ s : List Byte, s.length ≤ 9 → P s
  | [], _ => h0
  | [a], _ => h1 a
  | [a, b], _ => h2 a b
  | [a, b, c], _ => h3 a b c
  | [a, b, c, d], _ => h4 a b c d
  | [a, b, c, d, e], _ => h5 a b c d e
  | [a, b, c, d, e, f], _ => h6 a b c d e f
  | [a, b, c, d, e, f, g], _ => h7 a b c d e f g
  | [a, b, c, d, e, f, g, h], _ => h8 a b c d e f g h
  | [a, b, c, d, e, f, g, h, i], _ => h9 a b c d e f g h i
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hl => by simp at hl

/-! ## 1.2.3 equals the bit-vector specification -/

theorem deser123_long (s : List Byte) (h : 9 < s.length) : deser123 s = none := by
  cases s with
  | nil => simp at h
  | cons a t =>
    simp only [List.length_cons] at h
    simp [deser123]
    intro h1; omega

macro "reader_case" : tactic =>
  `(tactic| (intros; apply opt_eq <;>
      (simp [deser123, specBV, foldLow, magBV, negB, fitsBV, intMin] <;> bv_decide)))

theorem deser123_eq_specBV (s : List Byte) : deser123 s = specBV s := by
  by_cases h : s.length ≤ 9
  · revert s
    apply forall_len_le9
    · simp [deser123, specBV, magBV, negB, fitsBV]
    all_goals reader_case
  · rw [deser123_long s (by omega)]; simp [specBV, h]

/-! ## From bit vectors to integers -/

theorem magBV_toNat (s : List Byte) (h : s.length ≤ 9) : (magBV s).toNat = mag s := by
  revert s
  apply forall_len_le9 <;> intros <;> simp [magBV, mag] <;> bv_omega

/-- **Main theorem.** The 1.2.3 reader accepts exactly the strings of at most
nine bytes whose denoted integer fits in `int64_t`, and returns that integer. -/
theorem deser123_spec (s : List Byte) :
    deser123 s =
      if s.length ≤ 9 ∧ -2 ^ 63 ≤ denote s ∧ denote s < 2 ^ 63
      then some (BitVec.ofInt 64 (denote s)) else none := by
  rw [deser123_eq_specBV, specBV]
  by_cases hl : s.length ≤ 9
  · have hm := magBV_toNat s hl
    have hlt := (magBV s).isLt
    cases hn : negB s
    · have e : BitVec.setWidth 64 (magBV s) = BitVec.ofNat 64 (mag s) := by
        apply BitVec.eq_of_toNat_eq; simp [hm]
      simp [fitsBV, denote, hn, hl, BitVec.ult, hm, e]
      by_cases c : mag s < 9223372036854775808
      · have c' : (mag s : Int) < 9223372036854775808 := by omega
        simp [c, c']
      · have c' : ¬ (mag s : Int) < 9223372036854775808 := by omega
        simp [c, c']
    · have e : -BitVec.setWidth 64 (magBV s) = BitVec.ofInt 64 (-(mag s : Int)) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofInt, hm]
        omega
      simp [fitsBV, denote, hn, hl, BitVec.ule, hm, e]
      by_cases c : mag s ≤ 9223372036854775808
      · have c' : (mag s : Int) ≤ 9223372036854775808 ∧ -(mag s : Int) < 9223372036854775808 := by
          omega
        simp [c, c']
      · have c' : ¬ ((mag s : Int) ≤ 9223372036854775808 ∧ -(mag s : Int) < 9223372036854775808) := by
          omega
        simp [c, c']
  · simp [hl]

/-- Accepted values are the denoted integer, as a signed 64-bit value. -/
theorem deser123_toInt (s : List Byte) (v : I64) (h : deser123 s = some v) :
    v.toInt = denote s := by
  rw [deser123_spec] at h
  split at h
  · rename_i c
    simp only [Option.some.injEq] at h
    subst h
    rw [BitVec.toInt_ofInt]
    have := c.2.1; have := c.2.2
    simp [Int.bmod]; omega
  · simp at h

/-- Length alone rejects: a ten-byte string denoting 1 is refused. -/
example : denote [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 1 ∧
    deser123 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] = none := by
  constructor
  · decide
  · exact deser123_long _ (by decide)

/-- The reader does not require minimal encoding: padding up to nine bytes is
accepted, and so is negative zero. -/
example : deser123 [1, 0, 0, 0, 0, 0, 0, 0, 0] = some 1 := by decide
example : deser123 [1, 0] = some 1 := by decide
example : deser123 [0x80] = some 0 := by decide

/-! ## 1.2.3 reaches no undefined operation -/

theorem opt2_eq {a : Option (Option I64)} {b : Option I64}
    (h1 : a.isSome = true) (h2 : a.getD none = b) : a = some b := by
  cases a <;> simp_all

@[simp] theorem getD_map_some {α} (o : Option α) : (o.map some).getD none = o := by
  cases o <;> rfl

macro "checked_case" : tactic =>
  `(tactic| (intros; apply opt2_eq
             · simp [deser123?, foldLow?, shl?, neg?, intMin] <;> bv_decide
             · apply opt_eq <;>
                 (simp [deser123?, deser123, foldLow?, foldLow, shl?, neg?, intMin] <;> bv_decide)))

/-- On every input the checked reader finishes without reaching a shift by 64
or more or a negation of `INT64_MIN`, and agrees with `deser123`. -/
theorem deser123?_eq (s : List Byte) : deser123? s = some (deser123 s) := by
  by_cases h : s.length ≤ 9
  · revert s
    apply forall_len_le9
    · simp [deser123?, deser123]
    all_goals checked_case
  · rw [deser123_long s (by omega)]
    cases s with
    | nil => simp at h
    | cons a t =>
      simp only [List.length_cons] at h
      simp [deser123?]
      intro h1; omega

/-! ## 1.2.3 against 1.2.2 -/

macro "agree_case" : tactic =>
  `(tactic| first
      | (intro _ _ _ _ _ _ _ _ _ _ hl; simp at hl; done)
      | (intros; simp [deser123, deser122, foldLow, foldLowX86]))

/-- On one to eight bytes the two versions return the same value. -/
theorem deser123_eq_deser122_of_le8 (s : List Byte) (hne : s ≠ []) (h : s.length ≤ 8) :
    deser123 s = some (deser122 s) := by
  have key : ∀ s : List Byte, s.length ≤ 9 → s ≠ [] → s.length ≤ 8 →
      deser123 s = some (deser122 s) := by
    apply forall_len_le9
    · simp
    all_goals agree_case
  exact key s (by omega) hne h

/-- `bsv::IsMinimallyEncoded`, without its length limit. -/
def isMinimal : List Byte → Bool
  | [] => true
  | [b] => (b &&& 0x7f#8) != 0
  | [a, b] => (b &&& 0x7f#8) != 0 || (a &&& 0x80#8) != 0
  | _ :: c :: d :: bs => isMinimal (c :: d :: bs)

/-- Nine bytes. 1.2.2 returns the low eight bytes and never reads the ninth.
1.2.3 accepts only a ninth byte of 00 or 80, and then: with 00 it returns the
1.2.2 value; with 80 it returns the negation of the 1.2.2 value. Negation here
is modulo 2^64, so the two versions return the same value exactly when the low
eight bytes are zero or encode `INT64_MIN`. -/
theorem nine_bytes (a b c d e f g h i : Byte) (v : I64)
    (hv : deser123 [a, b, c, d, e, f, g, h, i] = some v) :
    (i = 0x00#8 ∨ i = 0x80#8) ∧
    (i = 0x00#8 → v = deser122 [a, b, c, d, e, f, g, h, i]) ∧
    (i = 0x80#8 → v = -deser122 [a, b, c, d, e, f, g, h, i]) := by
  rw [deser123_eq_specBV] at hv
  simp [specBV, fitsBV, magBV, negB] at hv
  obtain ⟨hf, rfl⟩ := hv
  simp [deser122, foldLowX86]
  bv_decide

/-- Nine bytes, minimally encoded: 1.2.3 accepts exactly one such string, the
encoding of `INT64_MIN`, and returns what 1.2.2 returns. -/
theorem nine_bytes_minimal (a b c d e f g h i : Byte) (v : I64)
    (hmin : isMinimal [a, b, c, d, e, f, g, h, i] = true)
    (hv : deser123 [a, b, c, d, e, f, g, h, i] = some v) :
    [a, b, c, d, e, f, g, h, i] = [0, 0, 0, 0, 0, 0, 0, 0x80, 0x80] ∧
    v = intMin ∧ v = deser122 [a, b, c, d, e, f, g, h, i] := by
  rw [deser123_eq_specBV] at hv
  simp [specBV, fitsBV, magBV, negB] at hv
  obtain ⟨hf, rfl⟩ := hv
  simp [isMinimal] at hmin
  simp [deser122, foldLowX86, intMin]
  bv_decide

/-- The two versions disagree on a non-minimal nine-byte negative: 1.2.2 reads
`05 00×7 80` as 5, 1.2.3 as −5. -/
example : deser122 [5, 0, 0, 0, 0, 0, 0, 0, 0x80] = 5 ∧
    deser123 [5, 0, 0, 0, 0, 0, 0, 0, 0x80] = some (-5) := by decide

/-- A nine-byte operand whose ninth byte carries magnitude: 1.2.2 returns the
low eight bytes (here 5), 1.2.3 refuses. -/
example : deser122 [5, 0, 0, 0, 0, 0, 0, 0, 1] = 5 ∧
    deser123 [5, 0, 0, 0, 0, 0, 0, 0, 1] = none := by decide

end Bsv.ScriptNum
