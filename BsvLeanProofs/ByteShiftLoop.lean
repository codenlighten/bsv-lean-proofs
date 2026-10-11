import BsvLeanProofs.ByteShift

/-!
# The byte-shift loops of OP_LSHIFT and OP_RSHIFT

Written from bitcoin-sv v1.2.3, `src/script/interpreter.cpp`, the static
functions `RShift` and `LShift` and the mask tables `make_rshift_mask` and
`make_lshift_mask`. Each is transcribed as the source writes it: a loop over
the byte index that ORs a shifted part and a carry into a zeroed result of
the same length. The result being built is a function from index to byte, so
"the OR of earlier writes" is a plain update.

`rshiftLoop_eq` and `lshiftLoop_eq` prove that the transcribed loop returns
exactly the arithmetic `natToBE` result that `ByteShift.lean` defines the
opcodes by, for every shift count and every length. They are theorems about
the Lean text; that the text is the source's is checked by test
(`difftest/shift_compare.sh`), not by proof.

Two things the transcription leaves out, both outside the range the opcodes
reach in practice:
- Indices are unbounded naturals, where the source uses `size_t`. They agree
  while no index sum wraps, which holds for any element that fits in memory
  with a count that fits an `int`.
- The opcode applies the helper once, with `n.getint()`, when the count is
  below the bit length; the source's repeat for counts above `INT32_MAX` (an
  element of more than 2^28 bytes) and its cancellation check are not
  modelled. `opLShiftSrc` and `opRShiftSrc` are the opcodes with the
  transcribed loop in place of the arithmetic, a single call.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-- `make_rshift_mask`: the bits that stay in the byte. -/
def rMask (b : Nat) : Byte := (0xFF#8) <<< b

/-- `make_lshift_mask`: the low `8 - b` bits. -/
def lMask (b : Nat) : Byte := (0xFF#8) >>> b

/-- One pass of the body of the source's `RShift` loop, for index `i`: OR the
shifted part into the result at `k = i + byte_shift` when `k` is in range, and
the carry into the next byte when that one is in range. -/
def rStep (x : List Byte) (n : Nat) (acc : Nat → Byte) (i : Nat) : Nat → Byte :=
  let bitShift := n % 8
  let byteShift := n / 8
  let mask := rMask bitShift
  let ov := ~~~mask
  let k := i + byteShift
  let acc1 : Nat → Byte :=
    if k < x.length then
      let v := ((x.getD i 0#8) &&& mask) >>> bitShift
      fun j => if j = k then acc j ||| v else acc j
    else acc
  if k + 1 < x.length then
    let c := ((x.getD i 0#8) &&& ov) <<< (8 - bitShift)
    fun j => if j = k + 1 then acc1 j ||| c else acc1 j
  else acc1

/-- The source's `RShift`: `x.size()` passes of `rStep` over a zeroed result. -/
def rshiftLoop (x : List Byte) (n : Nat) : List Byte :=
  (List.range x.length).map ((List.range x.length).foldl (rStep x n) (fun _ => 0#8))

/-- One pass of the body of the source's `LShift` loop. -/
def lStep (x : List Byte) (n : Nat) (acc : Nat → Byte) (i : Nat) : Nat → Byte :=
  let bitShift := n % 8
  let byteShift := n / 8
  let mask := lMask bitShift
  let ov := ~~~mask
  if byteShift ≤ i then
    let k := i - byteShift
    let v := ((x.getD i 0#8) &&& mask) <<< bitShift
    let acc1 : Nat → Byte := fun j => if j = k then acc j ||| v else acc j
    if k ≥ 1 then
      let c := ((x.getD i 0#8) &&& ov) >>> (8 - bitShift)
      fun j => if j = k - 1 then acc1 j ||| c else acc1 j
    else acc1
  else acc

/-- The source's `LShift`. The index runs downward, `x.size() - 1` to `0`. -/
def lshiftLoop (x : List Byte) (n : Nat) : List Byte :=
  (List.range x.length).map
    ((List.range x.length).reverse.foldl (lStep x n) (fun _ => 0#8))

/-! ## Bit level: one byte and its carry -/

theorem cases8 (b : Nat) (hb : b < 8) :
    b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega

theorem rP1 (c : Byte) (b : Nat) (hb : b < 8) :
    ((c &&& rMask b) >>> b).toNat = c.toNat / 2 ^ b := by
  rcases cases8 b hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [rMask] <;> revert c <;> decide

theorem rP2 (a : Byte) (b : Nat) (hb : b < 8) :
    ((a &&& ~~~rMask b) <<< (8 - b)).toNat = (a.toNat % 2 ^ b) * 2 ^ (8 - b) := by
  rcases cases8 b hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [rMask] <;> revert a <;> decide

theorem lP1 (c : Byte) (b : Nat) (hb : b < 8) :
    ((c &&& lMask b) <<< b).toNat = (c.toNat % 2 ^ (8 - b)) * 2 ^ b := by
  rcases cases8 b hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [lMask] <;> revert c <;> decide

theorem lP2 (a : Byte) (b : Nat) (hb : b < 8) :
    ((a &&& ~~~lMask b) >>> (8 - b)).toNat = a.toNat / 2 ^ (8 - b) := by
  rcases cases8 b hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [lMask] <;> revert a <;> decide

theorem pow_split (b : Nat) (hb : b ≤ 8) : 2 ^ b * 2 ^ (8 - b) = 256 := by
  rw [← Nat.pow_add]; have : b + (8 - b) = 8 := by omega
  rw [this]

theorem rpiece (a c : Byte) (b : Nat) (hb : b < 8) :
    (((c &&& rMask b) >>> b) ||| ((a &&& ~~~rMask b) <<< (8 - b))).toNat
      = c.toNat / 2 ^ b + (a.toNat % 2 ^ b) * 2 ^ (8 - b) := by
  rw [BitVec.toNat_or, rP1 c b hb, rP2 a b hb]
  have h1 : c.toNat / 2 ^ b < 2 ^ (8 - b) := by
    apply Nat.div_lt_of_lt_mul
    rw [pow_split b (by omega)]; have := c.isLt; omega
  have := Nat.two_pow_add_eq_or_of_lt h1 (a.toNat % 2 ^ b)
  rw [Nat.mul_comm (a.toNat % 2 ^ b), Nat.or_comm, ← this, Nat.add_comm]

theorem lpiece (a c : Byte) (b : Nat) (hb : b < 8) :
    (((c &&& lMask b) <<< b) ||| ((a &&& ~~~lMask b) >>> (8 - b))).toNat
      = (c.toNat % 2 ^ (8 - b)) * 2 ^ b + a.toNat / 2 ^ (8 - b) := by
  rw [BitVec.toNat_or, lP1 c b hb, lP2 a b hb]
  have h1 : a.toNat / 2 ^ (8 - b) < 2 ^ b := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, pow_split b (by omega)]; have := a.isLt; omega
  have := Nat.two_pow_add_eq_or_of_lt h1 (c.toNat % 2 ^ (8 - b))
  rw [Nat.mul_comm (c.toNat % 2 ^ (8 - b)), ← this, Nat.mul_comm]

/-! ## Arithmetic: one byte of `N / 2^n` and of `N * 2^n` -/

/-- `x · y = 256` and `e < x`: adding `e` below a multiple of `x` and reducing
mod 256 keeps the multiple's residue. -/
theorem mod256_split (x y A e : Nat) (h : x * y = 256) (he : e < x) :
    (x * A + e) % 256 = x * (A % y) + e := by
  have hy : 0 < y := by
    cases y with
    | zero => simp at h
    | succ _ => omega
  have h1 : x * A = (x * y) * (A / y) + x * (A % y) := by
    calc x * A = x * (y * (A / y) + A % y) := by rw [Nat.div_add_mod A y]
      _ = _ := by rw [Nat.mul_add, ← Nat.mul_assoc]
  have h2 : x * (A % y) + e < x * y := by
    have : A % y + 1 ≤ y := Nat.mod_lt A hy
    have := Nat.mul_le_mul_left x this
    rw [Nat.mul_add] at this; omega
  rw [← h, show x * A + e = (x * (A % y) + e) + (x * y) * (A / y) by rw [h1]; omega]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h2

/-- Byte `t` of `N / 2^n`, where `2^n = p · 256^t` and `p · q = 256`: it is built from
byte `t` and the low bits of byte `t + 1` of `N`. -/
theorem div_digit (N t p q : Nat) (h : p * q = 256) :
    N / (p * 256 ^ t) % 256 = (N / 256 ^ t % 256) / p + (N / 256 ^ (t + 1) % p) * q := by
  have hp : 0 < p := by
    cases p with
    | zero => simp at h
    | succ _ => omega
  have e1 : N / (p * 256 ^ t) = (N / 256 ^ t) / p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e2 : N / 256 ^ (t + 1) = N / 256 ^ t / 256 := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [e1, e2]
  generalize N / 256 ^ t = A
  have hA : A = p * (q * (A / 256)) + A % 256 := by
    rw [← Nat.mul_assoc, h]; have := Nat.div_add_mod A 256; omega
  have e3 : A / p = q * (A / 256) + (A % 256) / p :=
    (congrArg (· / p) hA).trans (by rw [Nat.mul_add_div hp])
  have hc : (A % 256) / p < q := by
    apply Nat.div_lt_of_lt_mul
    rw [h]; exact Nat.mod_lt _ (by omega)
  rw [e3, mod256_split q p _ _ (by rw [Nat.mul_comm]; exact h) hc]
  rw [Nat.mul_comm q, Nat.add_comm]

/-- The same for multiplication: byte `s + 1` of `N · p`. -/
theorem mul_digit (N s p q : Nat) (h : p * q = 256) :
    N * p / 256 ^ (s + 1) % 256 = (N / 256 ^ (s + 1) % q) * p + (N / 256 ^ s % 256) / q := by
  have hp : 0 < p := by
    cases p with
    | zero => simp at h
    | succ _ => omega
  have hq : 0 < q := by
    cases q with
    | zero => simp at h
    | succ _ => omega
  have e1 : N * p / 256 ^ (s + 1) = (N / 256 ^ s) / q := by
    rw [show 256 ^ (s + 1) = (256 ^ s * q) * p by
      rw [Nat.pow_succ, ← h, Nat.mul_assoc, Nat.mul_comm p q]]
    rw [Nat.mul_div_mul_right _ _ hp, ← Nat.div_div_eq_div_mul]
  have e2 : N / 256 ^ (s + 1) = N / 256 ^ s / 256 := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [e1, e2]
  generalize N / 256 ^ s = M
  have hA : M = q * (p * (M / 256)) + M % 256 := by
    rw [← Nat.mul_assoc, Nat.mul_comm q p, h]; have := Nat.div_add_mod M 256; omega
  have e3 : M / q = p * (M / 256) + (M % 256) / q :=
    (congrArg (· / q) hA).trans (by rw [Nat.mul_add_div hq])
  have hc : (M % 256) / q < p := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, h]; exact Nat.mod_lt _ (by omega)
  rw [e3, mod256_split p q _ _ h hc]
  rw [Nat.mul_comm p, Nat.add_comm]

/-- The least significant byte of `N · p`. -/
theorem mul_digit0 (N p q : Nat) (h : p * q = 256) :
    N * p % 256 = (N % 256 % q) * p := by
  have hq : q ∣ 256 := ⟨p, by rw [← h, Nat.mul_comm]⟩
  rw [Nat.mod_mod_of_dvd _ hq, ← h, Nat.mul_comm p q, Nat.mul_mod_mul_right]


/-! ## The folds in closed form -/

/-- The part the right-shift loop ORs in at the target byte, from source byte `i`. -/
def rV (x : List Byte) (n : Nat) (i : Nat) : Byte :=
  ((x.getD i 0#8) &&& rMask (n % 8)) >>> (n % 8)

/-- The carry the right-shift loop ORs into the byte after the target. -/
def rC (x : List Byte) (n : Nat) (i : Nat) : Byte :=
  ((x.getD i 0#8) &&& ~~~rMask (n % 8)) <<< (8 - n % 8)

/-- A pass of the right-shift loop, one result byte at a time. -/
theorem rStep_apply (x : List Byte) (n : Nat) (acc : Nat → Byte) (i j : Nat) :
    rStep x n acc i j =
      (acc j ||| (if j = i + n / 8 ∧ i + n / 8 < x.length then rV x n i else 0#8)) |||
        (if j = i + n / 8 + 1 ∧ i + n / 8 + 1 < x.length then rC x n i else 0#8) := by
  unfold rStep rV rC
  by_cases h1 : i + n / 8 < x.length <;> by_cases h2 : i + n / 8 + 1 < x.length <;>
    by_cases h3 : j = i + n / 8 <;> by_cases h4 : j = i + n / 8 + 1 <;> simp [h1, h2, h3, h4] <;> omega

/-- What the right-shift loop has written at index `j` after the first `m` passes:
the shifted part from `j - byte_shift` and the carry from `j - byte_shift - 1`. -/
theorem rfold (x : List Byte) (n : Nat) :
    ∀ (m j : Nat), (List.range m).foldl (rStep x n) (fun _ => 0#8) j =
      (if j < x.length ∧ n / 8 ≤ j ∧ j - n / 8 < m then rV x n (j - n / 8) else 0#8) |||
      (if j < x.length ∧ n / 8 + 1 ≤ j ∧ j - n / 8 - 1 < m then rC x n (j - n / 8 - 1) else 0#8)
  | 0, j => by simp
  | m + 1, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, rStep_apply,
      rfold x n m j]
    generalize rV x n = V
    generalize rC x n = C
    generalize x.length = L
    generalize n / 8 = bs
    by_cases hA : j = m + bs
    · subst hA
      have e1 : m + bs - bs = m := by omega
      simp only [e1, eq_self, true_and]
      repeat' split
      all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl
    · by_cases hB : j = m + bs + 1
      · subst hB
        have e1 : m + bs + 1 - bs = m + 1 := by omega
        simp only [e1, eq_self, true_and]
        repeat' split
        all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl
      · repeat' split
        all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl


/-- The part the left-shift loop ORs in at the target byte, from source byte `i`. -/
def lV (x : List Byte) (n : Nat) (i : Nat) : Byte :=
  ((x.getD i 0#8) &&& lMask (n % 8)) <<< (n % 8)

/-- The carry the left-shift loop ORs into the byte before the target. -/
def lC (x : List Byte) (n : Nat) (i : Nat) : Byte :=
  ((x.getD i 0#8) &&& ~~~lMask (n % 8)) >>> (8 - n % 8)

/-- A pass of the left-shift loop, one result byte at a time. -/
theorem lStep_apply (x : List Byte) (n : Nat) (acc : Nat → Byte) (i j : Nat) :
    lStep x n acc i j =
      (acc j ||| (if n / 8 ≤ i ∧ j = i - n / 8 then lV x n i else 0#8)) |||
        (if n / 8 ≤ i ∧ 1 ≤ i - n / 8 ∧ j = i - n / 8 - 1 then lC x n i else 0#8) := by
  unfold lStep lV lC
  dsimp only
  repeat' split
  all_goals try dsimp only
  repeat' split
  all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl

/-- The left-shift loop over a list of distinct source indices, in closed form. -/
theorem lfold (x : List Byte) (n : Nat) :
    ∀ (l : List Nat), l.Nodup → ∀ (acc : Nat → Byte) (j : Nat),
      l.foldl (lStep x n) acc j =
        (acc j ||| (if j + n / 8 ∈ l then lV x n (j + n / 8) else 0#8)) |||
        (if j + n / 8 + 1 ∈ l then lC x n (j + n / 8 + 1) else 0#8)
  | [], _, acc, j => by simp
  | a :: l, hnd, acc, j => by
    rw [List.foldl_cons, lfold x n l (List.nodup_cons.mp hnd).2, lStep_apply]
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    generalize lV x n = V
    generalize lC x n = C
    generalize n / 8 = bs
    simp only [List.mem_cons]
    by_cases h1 : a = j + bs
    · subst h1
      simp [ha]
      repeat' split
      all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl
    · by_cases h2 : a = j + bs + 1
      · subst h2
        simp [ha]
        repeat' split
        all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl
      · simp [Ne.symm h1, Ne.symm h2]
        repeat' split
        all_goals first | (exfalso; omega) | (simp; done) | (simp [BitVec.or_comm]; done) | ac_rfl


/-! ## Bytes of a big-endian value -/

theorem beNat_lt : ∀ x : List Byte, beNat x < 256 ^ x.length
  | [] => by simp [beNat]
  | b :: bs => by
    have ih := beNat_lt bs
    have hb := b.isLt
    simp only [beNat, List.length_cons, Nat.pow_succ]
    generalize bs.length = m at *
    have : (b.toNat + 1) * 256 ^ m ≤ 256 * 256 ^ m :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (256 ^ m) 256]
    omega

/-- Byte `i` of a big-endian string is digit `L - 1 - i` of its value. -/
theorem beNat_digit : ∀ (x : List Byte) (i : Nat) (hi : i < x.length),
    beNat x / 256 ^ (x.length - 1 - i) % 256 = (x[i]'hi).toNat
  | [], i, hi => by simp at hi
  | b :: bs, 0, _ => by
    have hR := beNat_lt bs
    have hb := b.isLt
    simp only [beNat, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 256)),
      Nat.div_eq_of_lt hR, Nat.zero_add]
    omega
  | b :: bs, i + 1, hi => by
    have hi' : i < bs.length := by simpa using hi
    have ih := beNat_digit bs i hi'
    have hR := beNat_lt bs
    simp only [beNat, List.length_cons, List.getElem_cons_succ]
    have e : bs.length + 1 - 1 - (i + 1) = bs.length - 1 - i := by omega
    rw [e]
    have e2 : 256 ^ bs.length = 256 ^ (bs.length - 1 - i) * 256 ^ (i + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hpos : 0 < 256 ^ (bs.length - 1 - i) := Nat.pow_pos (by decide)
    have hY : b.toNat * (256 ^ (bs.length - 1 - i) * 256 ^ (i + 1)) =
        256 ^ (bs.length - 1 - i) * ((b.toNat * 256 ^ i) * 256) := by
      rw [Nat.pow_succ]; ac_rfl
    rw [e2, hY, Nat.mul_add_div hpos, ← ih]
    generalize b.toNat * 256 ^ i = W
    generalize beNat bs / 256 ^ (bs.length - 1 - i) = Z
    omega

/-- `natToBE` lists its bytes from the most significant. -/
theorem natToBE_eq_map : ∀ (len N : Nat), natToBE len N =
    (List.range len).map (fun j => BitVec.ofNat 8 (N / 256 ^ (len - 1 - j) % 256))
  | 0, _ => by simp [natToBE]
  | len + 1, N => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [natToBE]
    congr 1
    rw [natToBE_eq_map len N]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    rw [Nat.sub_sub, Nat.add_comm 1 j]
    congr 3 <;> omega


theorem pow2_split (n : Nat) : 2 ^ n = 2 ^ (n % 8) * 256 ^ (n / 8) := by
  have h : 2 ^ (n % 8 + 8 * (n / 8)) = 2 ^ (n % 8) * 256 ^ (n / 8) := by
    rw [Nat.pow_add, Nat.pow_mul]
  rwa [Nat.mod_add_div] at h

theorem getD_toNat (x : List Byte) (i : Nat) (hi : i < x.length) :
    (x.getD i 0#8).toNat = (x[i]'hi).toNat := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- **The right-shift loop computes the arithmetic definition.** -/
theorem rshiftLoop_eq (x : List Byte) (n : Nat) :
    rshiftLoop x n = natToBE x.length (beNat x / 2 ^ n) := by
  unfold rshiftLoop
  rw [natToBE_eq_map]
  apply List.map_congr_left
  intro j hj
  have hjL : j < x.length := List.mem_range.mp hj
  rw [rfold x n x.length j]
  apply BitVec.eq_of_toNat_eq
  have hpq := pow_split (n % 8) (by omega)
  have hlt := beNat_lt x
  have hT : beNat x / 2 ^ n / 256 ^ (x.length - 1 - j) =
      beNat x / (2 ^ (n % 8) * 256 ^ (n / 8 + (x.length - 1 - j))) := by
    rw [pow2_split n, Nat.div_div_eq_div_mul, Nat.pow_add, Nat.mul_assoc]
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 8), hT]
  have hb8 : n % 8 < 8 := by omega
  by_cases hbs : n / 8 ≤ j
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + n / 8 := ⟨j - n / 8, by omega⟩
    have hiL : i < x.length := by omega
    have ht : n / 8 + (x.length - 1 - (i + n / 8)) = x.length - 1 - i := by omega
    have e : i + n / 8 - n / 8 = i := by omega
    have c1 : i + n / 8 < x.length ∧ n / 8 ≤ i + n / 8 ∧ i + n / 8 - n / 8 < x.length := by omega
    rw [ht, div_digit _ _ _ _ hpq, beNat_digit x i hiL, ite_eq_left_of_eq_true _ _ (eq_true c1)]
    have hc : (x.getD i 0#8).toNat = (x[i]'hiL).toNat := getD_toNat x i hiL
    by_cases hi0 : i = 0
    · subst hi0
      have hz : beNat x / 256 ^ (x.length - 1 - 0 + 1) = 0 :=
        Nat.div_eq_of_lt (by have : x.length - 1 - 0 + 1 = x.length := by omega
                             rw [this]; exact hlt)
      have c2 : ¬(0 + n / 8 < x.length ∧ n / 8 + 1 ≤ 0 + n / 8 ∧ 0 + n / 8 - n / 8 - 1 < x.length) := by
        omega
      rw [hz, ite_eq_right_of_eq_false _ _ (eq_false c2), BitVec.or_zero]
      simp only [rV, e, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
      rw [rP1 _ _ hb8, hc]
    · have c2 : i + n / 8 < x.length ∧ n / 8 + 1 ≤ i + n / 8 ∧
          i + n / 8 - n / 8 - 1 < x.length := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true c2)]
      have hl1 : x.length - 1 - i + 1 = x.length - 1 - (i - 1) := by omega
      have hd := beNat_digit x (i - 1) (by omega)
      have hdv : 2 ^ (n % 8) ∣ 256 := ⟨2 ^ (8 - n % 8), hpq.symm⟩
      rw [hl1, ← Nat.mod_mod_of_dvd (beNat x / 256 ^ (x.length - 1 - (i - 1))) hdv, hd]
      have e' : i + n / 8 - n / 8 - 1 = i - 1 := by omega
      unfold rV rC
      rw [e, rpiece _ _ _ hb8, hc, getD_toNat x (i - 1) (by omega)]
  · have hz : beNat x / (2 ^ (n % 8) * 256 ^ (n / 8 + (x.length - 1 - j))) = 0 := by
      apply Nat.div_eq_of_lt
      have h1 : 256 ^ x.length ≤ 256 ^ (n / 8 + (x.length - 1 - j)) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 256 ^ (n / 8 + (x.length - 1 - j)) ≤
          2 ^ (n % 8) * 256 ^ (n / 8 + (x.length - 1 - j)) :=
        Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      omega
    have c1 : ¬(j < x.length ∧ n / 8 ≤ j ∧ j - n / 8 < x.length) := by omega
    have c2 : ¬(j < x.length ∧ n / 8 + 1 ≤ j ∧ j - n / 8 - 1 < x.length) := by omega
    rw [hz, ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c2)]
    simp


/-- **The left-shift loop computes the arithmetic definition.** -/
theorem lshiftLoop_eq (x : List Byte) (n : Nat) :
    lshiftLoop x n = natToBE x.length (beNat x * 2 ^ n) := by
  unfold lshiftLoop
  rw [natToBE_eq_map]
  apply List.map_congr_left
  intro j hj
  have hjL : j < x.length := List.mem_range.mp hj
  have hnd : ((List.range x.length).reverse).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_reverse]
    exact List.Pairwise.imp (fun h => Ne.symm h) List.nodup_range
  rw [lfold x n _ hnd _ j]
  apply BitVec.eq_of_toNat_eq
  have hpq := pow_split (n % 8) (by omega)
  have hb8 : n % 8 < 8 := by omega
  have hdvq : 2 ^ (8 - n % 8) ∣ 256 := ⟨2 ^ (n % 8), by rw [← hpq, Nat.mul_comm]⟩
  have hT : beNat x * 2 ^ n / 256 ^ (x.length - 1 - j) =
      beNat x * 2 ^ (n % 8) * 256 ^ (n / 8) / 256 ^ (x.length - 1 - j) := by
    rw [pow2_split n, Nat.mul_assoc]
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 8), hT]
  simp only [List.mem_reverse, List.mem_range]
  by_cases hs : n / 8 ≤ x.length - 1 - j
  · have hjb : j + n / 8 < x.length := by omega
    obtain ⟨u, hu⟩ : ∃ u, x.length - 1 - j = u + n / 8 := ⟨x.length - 1 - j - n / 8, by omega⟩
    have hdiv : beNat x * 2 ^ (n % 8) * 256 ^ (n / 8) / 256 ^ (x.length - 1 - j) =
        beNat x * 2 ^ (n % 8) / 256 ^ u := by
      rw [hu, Nat.pow_add]
      exact Nat.mul_div_mul_right _ _ (Nat.pow_pos (by decide : 0 < 256))
    rw [hdiv, ite_eq_left_of_eq_true _ _ (eq_true hjb)]
    have hc := beNat_digit x (j + n / 8) hjb
    have e : x.length - 1 - (j + n / 8) = u := by omega
    rw [e] at hc
    have hcg := getD_toNat x (j + n / 8) hjb
    cases u with
    | zero =>
      have h1 : ¬ (j + n / 8 + 1 < x.length) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), BitVec.or_zero, BitVec.zero_or]
      rw [Nat.pow_zero, Nat.div_one, mul_digit0 _ _ _ hpq]
      rw [Nat.pow_zero, Nat.div_one] at hc
      unfold lV
      rw [lP1 _ _ hb8, hcg, ← hc]
    | succ u' =>
      have h1 : j + n / 8 + 1 < x.length := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), BitVec.zero_or, mul_digit _ _ _ _ hpq]
      have hc2 := beNat_digit x (j + n / 8 + 1) h1
      have e2 : x.length - 1 - (j + n / 8 + 1) = u' := by omega
      rw [e2] at hc2
      rw [← Nat.mod_mod_of_dvd (beNat x / 256 ^ (u' + 1)) hdvq, hc, hc2]
      unfold lV lC
      rw [lpiece _ _ _ hb8, hcg, getD_toNat x (j + n / 8 + 1) h1]
  · have h0 : ¬ (j + n / 8 < x.length) := by omega
    have h1 : ¬ (j + n / 8 + 1 < x.length) := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_right_of_eq_false _ _ (eq_false h1)]
    simp only [BitVec.or_zero, BitVec.toNat_zero]
    have hd : 256 ^ (n / 8) = 256 ^ (x.length - 1 - j) * (256 * 256 ^ (n / 8 - (x.length - 1 - j) - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    rw [hd, ← Nat.mul_assoc, Nat.mul_comm _ (256 ^ (x.length - 1 - j)), Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide)), Nat.mul_comm (beNat x * _)]
    rw [Nat.mul_assoc]
    exact (Nat.mul_mod_right _ _).symm


/-! ## The opcodes through the source's loops -/

/-- OP_LSHIFT with the source's loop in place of the arithmetic: the count is read,
a negative one refused, a count of at least the bit length zero-fills, and otherwise
one call of `LShift` runs. The source's repeat for counts above `INT32_MAX` and its
cancellation check are not modelled. -/
def opLShiftSrc (p : Params) : Stack → Except Err Stack
  | top :: x :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 then .error .invalidNumberRange
      else if n ≥ (x.length * 8 : Nat) then .ok (List.replicate x.length 0#8 :: st)
      else .ok (lshiftLoop x n.toNat :: st)
  | _ => .error .invalidStackOperation

/-- OP_RSHIFT with the source's loop in place of the arithmetic (see `opLShiftSrc`). -/
def opRShiftSrc (p : Params) : Stack → Except Err Stack
  | top :: x :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 then .error .invalidNumberRange
      else if n ≥ (x.length * 8 : Nat) then .ok (List.replicate x.length 0#8 :: st)
      else .ok (rshiftLoop x n.toNat :: st)
  | _ => .error .invalidStackOperation

/-- OP_LSHIFT defined arithmetically equals OP_LSHIFT through the transcribed loop,
for every count. This relates two Lean definitions; the source's chunking of counts
above `INT32_MAX` (reached only by an element of more than 2^28 bytes) is not
modelled. -/
theorem opLShift_eq_src (p : Params) (top x : Elem) (st : Stack) :
    opLShift p (top :: x :: st) = opLShiftSrc p (top :: x :: st) := by
  cases h : scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
  | error e => simp [opLShift, opLShiftSrc, h]
  | ok n =>
    by_cases h1 : n < 0
    · simp [opLShift, opLShiftSrc, h, h1]
    · simp [opLShift, opLShiftSrc, h, h1, lshiftLoop_eq]

/-- The same for OP_RSHIFT. -/
theorem opRShift_eq_src (p : Params) (top x : Elem) (st : Stack) :
    opRShift p (top :: x :: st) = opRShiftSrc p (top :: x :: st) := by
  cases h : scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
  | error e => simp [opRShift, opRShiftSrc, h]
  | ok n =>
    by_cases h1 : n < 0
    · simp [opRShift, opRShiftSrc, h, h1]
    · simp [opRShift, opRShiftSrc, h, h1, rshiftLoop_eq]

end Bsv.Splice
