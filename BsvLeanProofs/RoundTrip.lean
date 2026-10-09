import BsvLeanProofs.ScriptNum

/-!
# Encode then decode

A model of `bsv::serialize<int64_t>` (`src/script/int_serialization.h`, the same
text at v1.2.2 and v1.2.3) and a proof that the 1.2.3 reader inverts it on
every `int64_t`, and that its output is minimally encoded.

What is modelled: the body of `serialize` and of `bsv::abs`. The `while` loop
is run for at most eight rounds, which is enough for a 64-bit magnitude (if it
were not, the round-trip theorem below would fail).
-/

namespace Bsv.ScriptNum

/-- The loop of `serialize`, on the magnitude `a`. In the source `tmp` is
`a & 0xff` and the loop continues with `a >> 8`. -/
def serLoop : Nat → BitVec 64 → Bool → List Byte
  | 0, _, _ => []
  | fuel + 1, a, neg =>
    if a == 0 then []
    else if a >>> 8 != 0 then a.setWidth 8 :: serLoop fuel (a >>> 8) neg
    else if (a.setWidth 8 &&& 0x80#8) != 0 then [a.setWidth 8, if neg then 0x80#8 else 0#8]
    else [if neg then a.setWidth 8 ||| 0x80#8 else a.setWidth 8]

/-- `bsv::serialize<int64_t>`. The magnitude is `bsv::abs`, computed on
`uint64_t`, so it is defined for `INT64_MIN` too. -/
def ser (v : I64) : List Byte :=
  if v == 0 then [] else serLoop 8 (if v.slt 0 then -v else v) (v.slt 0)

theorem cons_ite {α} (c : Prop) [Decidable c] (a : α) (x y : List α) :
    (a :: (if c then x else y)) = if c then a :: x else a :: y := by split <;> rfl
theorem deser123_ite (c : Prop) [Decidable c] (x y : List Byte) :
    deser123 (if c then x else y) = if c then deser123 x else deser123 y := by split <;> rfl
theorem isMinimal_ite (c : Prop) [Decidable c] (x y : List Byte) :
    isMinimal (if c then x else y) = if c then isMinimal x else isMinimal y := by split <;> rfl

set_option maxHeartbeats 4000000 in
/-- **Round trip.** The 1.2.3 reader returns `n` on the encoding of `n`, for
every `int64_t` value. -/
theorem deser123_ser (n : I64) : deser123 (ser n) = some n := by
  unfold ser
  cases hneg : n.slt 0 <;>
  · simp only [serLoop, Bool.false_eq_true, ite_false, ite_true]
    simp only [cons_ite, deser123_ite]
    apply opt_eq <;>
      (simp [deser123, foldLow, intMin] <;> bv_decide)

set_option maxHeartbeats 4000000 in
/-- The encoding of every `int64_t` value is minimal. -/
theorem isMinimal_ser (n : I64) : isMinimal (ser n) = true := by
  unfold ser
  cases hneg : n.slt 0 <;>
  · simp only [serLoop, Bool.false_eq_true, ite_false, ite_true]
    simp only [cons_ite, isMinimal_ite, isMinimal]
    bv_decide

end Bsv.ScriptNum
