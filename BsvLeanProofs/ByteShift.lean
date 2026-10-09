import BsvLeanProofs.ShiftNum

/-!
# Reference semantics, slice 3: OP_LSHIFT and OP_RSHIFT

The two opcodes that shift a BYTE STRING, read as one big-endian number of
fixed width. Written from bitcoin-sv v1.2.3: `src/script/interpreter.cpp` (the
two `case` blocks and the helpers `LShift`, `RShift`).

What is modelled: the result as arithmetic on the big-endian value: a left
shift multiplies by `2^n` and keeps the low `8 · length` bits; a right shift
divides by `2^n`. The length never changes. The count is read with the era's
number reader and a negative count is refused.
What differs from the source: the source moves bytes and bits in a loop, and
for counts above `INT32_MAX` applies the helper in chunks (which needs an
element longer than 268 MB to be reached). That the loop computes this
arithmetic is NOT proved here; the vectors are the evidence.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-- The big-endian value of a byte string. -/
def beNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + beNat bs

/-- The `len`-byte big-endian string of `n` (its low `8 · len` bits). -/
def natToBE : Nat → Nat → List Byte
  | 0, _ => []
  | len + 1, n => BitVec.ofNat 8 (n / 256 ^ len % 256) :: natToBE len n

/-- OP_LSHIFT `(x n -- x << n)`, on a byte string. -/
def opLShift (p : Params) : Stack → Except Err Stack
  | top :: x :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 then .error .invalidNumberRange
      else if n ≥ (x.length * 8 : Nat) then .ok (List.replicate x.length 0#8 :: st)
      else .ok (natToBE x.length (beNat x * 2 ^ n.toNat) :: st)
  | _ => .error .invalidStackOperation

/-- OP_RSHIFT `(x n -- x >> n)`, on a byte string. -/
def opRShift (p : Params) : Stack → Except Err Stack
  | top :: x :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 then .error .invalidNumberRange
      else if n ≥ (x.length * 8 : Nat) then .ok (List.replicate x.length 0#8 :: st)
      else .ok (natToBE x.length (beNat x / 2 ^ n.toNat) :: st)
  | _ => .error .invalidStackOperation

/-! ## Properties -/

theorem length_natToBE : ∀ (len n : Nat), (natToBE len n).length = len
  | 0, _ => rfl
  | len + 1, n => by simp [natToBE, length_natToBE len n]

/-- Both opcodes keep the element's length. -/
theorem opLShift_length (p : Params) (top x : Elem) (st r : Stack)
    (h : opLShift p (top :: x :: st) = .ok r) : ∃ y : Elem, r = y :: st ∧ y.length = x.length := by
  simp only [opLShift] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm, by simp⟩
      · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm, length_natToBE _ _⟩

theorem opRShift_length (p : Params) (top x : Elem) (st r : Stack)
    (h : opRShift p (top :: x :: st) = .ok r) : ∃ y : Elem, r = y :: st ∧ y.length = x.length := by
  simp only [opRShift] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm, by simp⟩
      · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm, length_natToBE _ _⟩

end Bsv.Splice
