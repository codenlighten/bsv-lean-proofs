import BsvLeanProofs.MinimalUnique

/-!
# Reference semantics, slice 2: OP_LSHIFTNUM and OP_RSHIFTNUM

The two Chronicle opcodes that shift a NUMBER (as opposed to OP_LSHIFT and
OP_RSHIFT, which shift a byte string). Written from bitcoin-sv v1.2.3:
`src/script/interpreter.cpp` (the two `case` blocks), `script_num.cpp`
(`CScriptNum::operator<<=`, `operator>>=`, big-integer branch) and `big_int.cpp`
(`bint::operator<<=`, `operator>>=`).

Both opcodes read both operands with the big-integer reader, whatever the era.
What is modelled: the result or the error, including two rules that are not
arithmetic: OP_LSHIFTNUM refuses when the operand's length plus the shift in
whole bytes exceeds `MaxScriptNumLength`, before shifting; and OP_RSHIFTNUM
refuses a shift count above `INT_MAX` with a big-integer error, where the
arithmetic answer would be zero.
What is assumed: `bint` arithmetic is integer arithmetic, `BN_lshift` multiplies
by a power of two keeping the sign, `BN_rshift` shifts the magnitude (division
rounding toward zero), and `serialized_size`/`getvch` give the minimal encoding.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

def intMaxC : Int := 2147483647

/-- Little-endian bytes of a natural number, no padding. -/
def natBytesLoop : Nat → Nat → List Byte
  | 0, _ => []
  | fuel + 1, n => if n == 0 then [] else BitVec.ofNat 8 (n % 256) :: natBytesLoop fuel (n / 256)

def natBytes (n : Nat) : List Byte := natBytesLoop (n + 1) n

/-- The minimal encoding of an integer: magnitude bytes, an explicit sign byte,
then `MinimallyEncode`. (`getvch` of a big integer.) -/
def encInt (n : Int) : Elem :=
  minEnc (natBytes n.natAbs ++ [if n < 0 then 0x80#8 else 0x00#8])

/-- The numeric errors, extended with the big-integer error. -/
inductive ShiftErr
  | base (e : Err)
  | bigInt
  deriving DecidableEq, Repr

def liftErr {α} : Except Err α → Except ShiftErr α
  | .ok a => .ok a
  | .error e => .error (.base e)

/-- OP_LSHIFTNUM `(x n -- x · 2^n)`. -/
def opLShiftNum (p : Params) : Stack → Except ShiftErr Stack
  | s0 :: s1 :: st =>
    match scriptNum p.requireMinimal p.maxNumLen true s0 with
    | .error e => .error (.base e)
    | .ok n =>
      if n < 0 then .error (.base .invalidNumberRange)
      else match scriptNum p.requireMinimal p.maxNumLen true s1 with
        | .error e => .error (.base e)
        | .ok v =>
          -- refused before shifting: current size plus whole bytes of shift
          if ((encInt v).length : Int) + n / 8 > (p.maxNumLen : Int) then
            .error (.base .scriptNumOverflow)
          else if n > intMaxC then .error .bigInt
          else
            let r := encInt (v * 2 ^ n.toNat)
            if r.length > p.maxNumLen then .error (.base .scriptNumOverflow)
            else .ok (r :: st)
  | _ => .error (.base .invalidStackOperation)

/-- Division by `2^k` rounding toward zero, as `BN_rshift` does on the magnitude. -/
def shrZero (v : Int) (k : Nat) : Int :=
  if v < 0 then -((v.natAbs >>> k : Nat) : Int) else ((v.natAbs >>> k : Nat) : Int)

/-- OP_RSHIFTNUM `(x n -- x / 2^n, rounded toward zero)`. -/
def opRShiftNum (p : Params) : Stack → Except ShiftErr Stack
  | s0 :: s1 :: st =>
    match scriptNum p.requireMinimal p.maxNumLen true s0 with
    | .error e => .error (.base e)
    | .ok n =>
      if n < 0 then .error (.base .invalidNumberRange)
      else match scriptNum p.requireMinimal p.maxNumLen true s1 with
        | .error e => .error (.base e)
        | .ok v =>
          if n > intMaxC then .error .bigInt
          else .ok (encInt (shrZero v n.toNat) :: st)
  | _ => .error (.base .invalidStackOperation)

/-- The activation gate, for these two opcodes. -/
def chronicleGateS (p : Params) (op : Params → Stack → Except ShiftErr Stack) (st : Stack) :
    Except ShiftErr Stack :=
  if p.chronicleOps then op p st
  else if p.discourageNops then .error (.base .discourageUpgradableNops)
  else .ok st

/-! ## Properties -/

theorem natLE_natBytesLoop : ∀ (fuel n : Nat), n < fuel → natLE (natBytesLoop fuel n) = n
  | 0, n, h => by omega
  | fuel + 1, n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [natBytesLoop, natLE]
    · have ih := natLE_natBytesLoop fuel (n / 256) (by omega)
      have hb : (BitVec.ofNat 8 (n % 256)).toNat = n % 256 := by
        simp [BitVec.toNat_ofNat]
      simp only [natBytesLoop, h0, beq_iff_eq, ite_false, natLE, ih, hb]
      omega

theorem natLE_natBytes (n : Nat) : natLE (natBytes n) = n :=
  natLE_natBytesLoop (n + 1) n (by omega)

/-- `encInt n` denotes `n`. -/
theorem denote_encInt (n : Int) : denote (encInt n) = n := by
  unfold encInt
  rw [denote_minEnc, denote_snoc, natLE_natBytes]
  by_cases hn : n < 0
  · have hm : (0x80#8 : Byte).msb = true := by decide
    have hl : (0x80#8 : Byte).toNat % 128 = 0 := by decide
    simp only [hn, ite_true, hm, hl]
    simp; omega
  · have hm : (0x00#8 : Byte).msb = false := by decide
    have hl : (0x00#8 : Byte).toNat % 128 = 0 := by decide
    simp only [hn, ite_false, hm, hl]
    simp; omega

/-- `encInt n` is minimally encoded. -/
theorem isMinimal_encInt (n : Int) : isMinimal (encInt n) = true := isMinimal_minEnc _

/-- `encInt` is the canonical encoding: `MinimallyEncode` of any string is the
encoding of the integer it denotes. -/
theorem encInt_denote (s : Elem) : encInt (denote s) = minEnc s :=
  (minEnc_eq_of_minimal s (encInt (denote s)) (isMinimal_encInt _) (denote_encInt _)).symm

/-- **OP_LSHIFTNUM.** On success the result is the minimal encoding of
`x · 2^n`, where `x` and `n ≥ 0` are the integers the two operands hold. -/
theorem opLShiftNum_ok (p : Params) (s0 s1 : Elem) (st r : Stack)
    (h : opLShiftNum p (s0 :: s1 :: st) = .ok r) :
    ∃ n v : Int, scriptNum p.requireMinimal p.maxNumLen true s0 = .ok n ∧
      scriptNum p.requireMinimal p.maxNumLen true s1 = .ok v ∧ 0 ≤ n ∧
      r = encInt (v * 2 ^ n.toNat) :: st ∧ denote (encInt (v * 2 ^ n.toNat)) = v * 2 ^ n.toNat := by
  simp only [opLShiftNum] at h
  split at h
  · simp at h
  · rename_i n hn
    split at h
    · simp at h
    · rename_i hneg
      split at h
      · simp at h
      · rename_i v hv
        split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq] at h
              exact ⟨n, v, hn, hv, by omega, h.symm, denote_encInt _⟩

/-- **OP_RSHIFTNUM.** On success the count is at most `INT_MAX` and the result
is the minimal encoding of `x` divided by `2^n` rounding toward zero. -/
theorem opRShiftNum_ok (p : Params) (s0 s1 : Elem) (st r : Stack)
    (h : opRShiftNum p (s0 :: s1 :: st) = .ok r) :
    ∃ n v : Int, scriptNum p.requireMinimal p.maxNumLen true s0 = .ok n ∧
      scriptNum p.requireMinimal p.maxNumLen true s1 = .ok v ∧ 0 ≤ n ∧ n ≤ intMaxC ∧
      r = encInt (shrZero v n.toNat) :: st ∧
      denote (encInt (shrZero v n.toNat)) = shrZero v n.toNat := by
  simp only [opRShiftNum] at h
  split at h
  · simp at h
  · rename_i n hn
    split at h
    · simp at h
    · rename_i hneg
      split at h
      · simp at h
      · rename_i v hv
        split at h
        · simp at h
        · rename_i hbig
          simp only [Except.ok.injEq] at h
          exact ⟨n, v, hn, hv, by omega, by omega, h.symm, denote_encInt _⟩

/-- **The non-arithmetic rule of OP_RSHIFTNUM.** When both operands are read
and the count is above `INT_MAX`, the opcode fails with the big-integer error,
whatever the value, although the arithmetic result would be zero. -/
theorem opRShiftNum_big (p : Params) (s0 s1 : Elem) (st : Stack) (n v : Int)
    (hn : scriptNum p.requireMinimal p.maxNumLen true s0 = .ok n)
    (hv : scriptNum p.requireMinimal p.maxNumLen true s1 = .ok v) (hbig : intMaxC < n) :
    opRShiftNum p (s0 :: s1 :: st) = .error .bigInt := by
  have h0 : ¬ n < 0 := by simp only [intMaxC] at hbig; omega
  simp [opRShiftNum, hn, hv, h0, hbig]

/-- `shrZero` is division by `2^k` rounding toward zero. -/
theorem shrZero_eq_tdiv (v : Int) (k : Nat) : shrZero v k = Int.tdiv v (2 ^ k) := by
  unfold shrZero
  have hp : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  rw [Nat.shiftRight_eq_div_pow]
  by_cases hv : v < 0
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, v = -(m : Int) := ⟨v.natAbs, by omega⟩
    simp only [hv, ite_true, Int.natAbs_neg, Int.natAbs_natCast, Int.neg_tdiv]
    norm_cast
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, v = (m : Int) := ⟨v.natAbs, by omega⟩
    simp only [hv, ite_false, Int.natAbs_natCast]
    norm_cast

end Bsv.Splice
