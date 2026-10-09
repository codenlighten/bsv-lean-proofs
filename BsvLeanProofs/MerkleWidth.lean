import BsvLeanProofs.MerkleLiteral

/-!
# The counter width of the constant-space Merkle computation

`MerkleLiteral` uses an unbounded `count`. The source uses `uint32_t count`, an
array `inner` of 32 entries and shifts `1 << level` on 32 bits. This file adds
the width as a parameter `W` (the source has `W = 32`) and checks every
operation that the width can break.

What is modelled: the same computation with `count` reduced modulo `2^W` after
each addition (unsigned wrap-around), and an error raised when `1 << level` is
evaluated with `level ≥ W` (undefined in C++) or `inner[level]` is used with
`level ≥ W` (out of bounds).
What is proved: for every `W ≥ 1`, with at most `2^(W-1)` leaves the computation
raises no error and returns the tree's root (`rootW_eq`).
The converse, that more leaves always fault, is proved in `MerkleWidthExact`;
this file also checks it by evaluation for every count from `2^(W-1) + 1` to
`2^W + 3` at widths 1 to 6.
Also proved: the mutation flag at width `W`, for fewer than `2^W` leaves.
The branch output at width `W` is in `MerkleWidthBranch`. What is not modelled:
the Rust port's behaviour, which panics on the overflowing addition where
C++ wraps.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

inductive Fault
  | shift      -- `1 << level` with `level ≥ W`
  | fuel       -- the step budget ran out (never happens; see the theorems)
  deriving DecidableEq, Repr

/-- `!(count & (1 << level))`, refusing a shift by `W` or more. Every array
access in the computation is at a level that has just passed this test. -/
def bitClearW (W count level : Nat) : Except Fault Bool :=
  if level < W then .ok (bitClear count level) else .error .shift

section
variable [DecidableEq α]

def leafCarryW (W : Nat) (inner : Nat → α) (count : Nat) :
    Nat → Nat → α → Bool → Except Fault (Nat × α × Bool)
  | 0, _, _, _ => .error .fuel
  | fuel + 1, level, h, m =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true =>
      leafCarryW W inner count fuel (level + 1) (H (inner level) h) (m || inner level == h)
    | .ok false => .ok (level, h, m)

def addLeafW (W : Nat) (s : Lit α) (leaf : α) : Except Fault (Lit α) :=
  let c := (s.count + 1) % 2 ^ W
  match leafCarryW H W s.inner c (s.count + 1) 0 leaf s.mutated with
  | .error e => .error e
  | .ok r => .ok { inner := upd s.inner r.1 r.2.1, count := c, mutated := r.2.2 }

def runLeavesW (W : Nat) : Lit α → List α → Except Fault (Lit α)
  | s, [] => .ok s
  | s, a :: t =>
    match addLeafW H W s a with
    | .error e => .error e
    | .ok s' => runLeavesW W s' t

end

def skipLowW (W count : Nat) : Nat → Nat → Except Fault Nat
  | 0, _ => .error .fuel
  | fuel + 1, level =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true => skipLowW W count fuel (level + 1)
    | .ok false => .ok level

def sweepInnerW (W : Nat) (inner : Nat → α) (count : Nat) :
    Nat → Nat → α → Except Fault (Nat × α)
  | 0, _, _ => .error .fuel
  | fuel + 1, level, h =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true => sweepInnerW W inner count fuel (level + 1) (H (inner level) h)
    | .ok false => .ok (level, h)

def sweepOuterW (W : Nat) (inner : Nat → α) (F : Nat) : Nat → Nat → Nat → α → Except Fault α
  | 0, _, _, _ => .error .fuel
  | fuel + 1, count, level, h =>
    if level < W then
      if count != 1 <<< level then
        (sweepInnerW H W inner ((count + 1 <<< level) % 2 ^ W) F (level + 1) (H h h)).bind
          fun r => sweepOuterW W inner F fuel ((count + 1 <<< level) % 2 ^ W) r.1 r.2
      else .ok h
    else .error .shift

/-- Find the lowest occupied level, then sweep. -/
def finishW (W : Nat) (inner : Nat → α) (F fo count fs lvl : Nat) : Except Fault (Option α) :=
  (skipLowW W count fs lvl).bind fun level =>
    (sweepOuterW H W inner F fo count level (inner level)).bind fun h => .ok (some h)

section
variable [DecidableEq α] [Inhabited α]

/-- The root with a `W`-bit counter. -/
def rootW (W : Nat) (l : List α) : Except Fault (Option α) :=
  match l with
  | [] => .ok none
  | _ =>
    (runLeavesW H W start l).bind fun s =>
      finishW H W s.inner (s.count + 1) (s.count + 1) s.count (s.count + 1) 0

end

/-! ## With at most `2^(W-1)` leaves nothing faults -/

theorem level_lt_of_pow_le {W c lvl : Nat} (h1 : 2 ^ lvl ≤ c) (h2 : c < 2 ^ W) : lvl < W := by
  apply Nat.lt_of_not_le
  intro hle
  have := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

theorem pow_le_of_div_pos {c lvl q : Nat} (h : c / 2 ^ lvl = q + 1) : 2 ^ lvl ≤ c := by
  apply Nat.le_of_not_lt
  intro hlt
  rw [Nat.div_eq_of_lt hlt] at h
  omega

theorem pow_le_mul {q lvl : Nat} (hq : q ≠ 0) : 2 ^ lvl ≤ q * 2 ^ lvl :=
  Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

/-- The step the sweep takes stays below the same power of two. -/
theorem sweep_bound {p L B : Nat} (h : (p + 1) * 2 ^ L ≤ 2 ^ B) (heven : p % 2 = 0)
    (hp : p ≠ 0) : (p + 2) * 2 ^ L ≤ 2 ^ B := by
  have hL : L < B := by
    apply Nat.lt_of_not_le
    intro hle
    have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have h2 : 3 * 2 ^ L ≤ (p + 1) * 2 ^ L := Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.two_pow_pos L
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hL
  have hB : 2 ^ B = 2 ^ (k + 1) * 2 ^ L := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hB] at h ⊢
  have h1 : p + 1 ≤ 2 ^ (k + 1) := Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos L)
  have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
  exact Nat.mul_le_mul_right _ (by omega)

section
variable [DecidableEq α]

theorem leafCarryW_eq (W : Nat) (inner : Nat → α) (c : Nat) (hc : c < 2 ^ W) :
    ∀ (q lvl fuel : Nat) (h : α) (m : Bool),
    c / 2 ^ lvl = q + 1 → (absFrom inner lvl q).length < fuel →
    leafCarryW H W inner c fuel lvl h m = .ok (leafCarry H inner c fuel lvl h m) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fuel h m hq hfuel
    match fuel, hfuel with
    | 0, hfuel => omega
    | f + 1, hfuel =>
      have hlvl : lvl < W := level_lt_of_pow_le (pow_le_of_div_pos hq) hc
      have hbit : bitClear c lvl = decide ((q + 1) % 2 = 0) := by rw [bitClear_eq, hq]
      by_cases hodd : q % 2 = 1
      · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
        have hq' : c / 2 ^ (lvl + 1) = q / 2 + 1 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hq]; omega
        have hold := absFrom_pos inner lvl q (by omega)
        simp only [hodd, ite_true] at hold
        have hlen : (absFrom inner (lvl + 1) (q / 2)).length < f := by
          rw [hold] at hfuel; simpa using hfuel
        simp only [leafCarryW, leafCarry, bitClearW, hlvl, ite_true, hclear]
        exact ih (q / 2) (by omega) (lvl + 1) f _ _ hq' hlen
      · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
        simp [leafCarryW, leafCarry, bitClearW, hlvl, hstop]

theorem addLeafW_eq (W : Nat) (s : Lit α) (leaf : α) (hc : s.count + 1 < 2 ^ W) :
    addLeafW H W s leaf = .ok (addLeaf H s leaf) := by
  have hlen := length_absFrom_le s.inner s.count 0
  have hmod : (s.count + 1) % 2 ^ W = s.count + 1 := Nat.mod_eq_of_lt hc
  have := leafCarryW_eq H W s.inner (s.count + 1) hc s.count 0 (s.count + 1) leaf s.mutated
    (by simp) (by omega)
  simp only [addLeafW, hmod, this, addLeaf]

theorem runLeavesW_eq (W : Nat) : ∀ (l : List α) (s : Lit α), s.count + l.length < 2 ^ W →
    runLeavesW H W s l = .ok (runLeaves H s l)
  | [], s, _ => rfl
  | a :: t, s, hc => by
    simp only [List.length_cons] at hc
    have h3 := (addLeaf_spec H s a).2.2
    simp only [runLeavesW, addLeafW_eq H W s a (by omega)]
    exact runLeavesW_eq W t (addLeaf H s a) (by rw [h3]; omega)

end

theorem sweepW_carry (W B : Nat) (hB : B < W) (inner : Nat → α) (F : Nat) :
    ∀ (p L fi fo : Nat) (h : α) (cc : Nat),
    cc = (p + 1) * 2 ^ L → cc ≤ 2 ^ B →
    (absFrom inner L p).length < fi → (absFrom inner L p).length < F →
    (absFrom inner L p).length < fo →
    (sweepInnerW H W inner cc fi L h).bind (fun r => sweepOuterW H W inner F fo cc r.1 r.2) =
      .ok (sweepOuter H inner F fo cc (sweepInner H inner cc fi L h).1
        (sweepInner H inner cc fi L h).2) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h cc hcc hbound hfi hF hfo
    have hL : L < W := level_lt_of_pow_le (c := cc) (by rw [hcc]; exact pow_le_mul (by omega))
      (by omega)
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      match fo, hfo with
      | 0, hfo => omega
      | g + 1, hfo =>
        by_cases hp : p = 0
        · subst hp
          have hstop : bitClear cc L = false := by rw [hbit]; simp
          have hne : (cc != 1 <<< L) = false := by rw [hcc, ne_one_shiftLeft]; simp
          simp [sweepInnerW, sweepInner, bitClearW, hL, hstop, Except.bind, sweepOuterW,
            sweepOuter, hne]
        · have hold := absFrom_pos inner L p hp
          by_cases hodd : p % 2 = 1
          · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
            simp only [hodd, ite_true] at hold
            have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
              congr 1; omega
            rw [hold] at hfi hF hfo
            simp only [List.length_cons] at hfi hF hfo
            simp only [sweepInnerW, sweepInner, bitClearW, hL, ite_true, hclear]
            exact ih (p / 2) (by omega) (L + 1) f (g + 1) _ cc hcc' hbound (by omega) (by omega)
              (by omega)
          · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
            simp only [hodd, ite_false] at hold
            rw [hold] at hfi hF hfo
            simp only [List.length_cons] at hfi hF hfo
            have hne : (cc != 1 <<< L) = true := by
              rw [hcc, ne_one_shiftLeft]; simp; omega
            have hstep : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
              congr 1; omega
            have hb2 : cc + 1 <<< L ≤ 2 ^ B := by
              rw [hcc, add_one_shiftLeft]
              exact sweep_bound (by rw [← hcc]; exact hbound) (by omega) hp
            have hmod : (cc + 1 <<< L) % 2 ^ W = cc + 1 <<< L := Nat.mod_eq_of_lt (by omega)
            have e1 : sweepInnerW H W inner cc (f + 1) L h = .ok (L, h) := by
              simp [sweepInnerW, bitClearW, hL, hstop]
            have e2 : sweepInner H inner cc (f + 1) L h = (L, h) := by
              simp [sweepInner, hstop]
            have e3 : sweepOuterW H W inner F (g + 1) cc L h =
                (sweepInnerW H W inner (cc + 1 <<< L) F (L + 1) (H h h)).bind
                  (fun r => sweepOuterW H W inner F g (cc + 1 <<< L) r.1 r.2) := by
              simp only [sweepOuterW, hL, ite_true, hne, hmod]
            have e4 : sweepOuter H inner F (g + 1) cc L h =
                sweepOuter H inner F g (cc + 1 <<< L)
                  (sweepInner H inner (cc + 1 <<< L) F (L + 1) (H h h)).1
                  (sweepInner H inner (cc + 1 <<< L) F (L + 1) (H h h)).2 := by
              simp only [sweepOuter, hne, ite_true]
            rw [e1, e2]
            change sweepOuterW H W inner F (g + 1) cc L h = .ok (sweepOuter H inner F (g + 1) cc L h)
            rw [e3, e4]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ hstep hb2 (by omega) (by omega) (by omega)

theorem sweepW_top (W B : Nat) (hB : B < W) (inner : Nat → α) (F : Nat) (q lvl fo : Nat) (h : α)
    (c : Nat) (hc : c = q * 2 ^ lvl) (hbound : c ≤ 2 ^ B) (hodd : q % 2 = 1)
    (hF : (absFrom inner (lvl + 1) (q / 2)).length < F)
    (hfo : (absFrom inner (lvl + 1) (q / 2)).length + 1 < fo) :
    sweepOuterW H W inner F fo c lvl h = .ok (sweepOuter H inner F fo c lvl h) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul (by omega))
    (by omega)
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    by_cases hq : q = 1
    · subst hq
      have hne : (c != 1 <<< lvl) = false := by rw [hc, ne_one_shiftLeft]; simp
      simp [sweepOuterW, sweepOuter, hL, hne]
    · have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
      have hstep : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
        rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
        congr 1; omega
      have hb2 : c + 1 <<< lvl ≤ 2 ^ B := by
        rw [hc, add_one_shiftLeft]
        have : (q - 1 + 1) * 2 ^ lvl ≤ 2 ^ B := by
          have e : q - 1 + 1 = q := by omega
          rw [e, ← hc]; exact hbound
        have := sweep_bound this (by omega) (by omega)
        have e : q - 1 + 2 = q + 1 := by omega
        rwa [e] at this
      have hmod : (c + 1 <<< lvl) % 2 ^ W = c + 1 <<< lvl := Nat.mod_eq_of_lt (by omega)
      simp only [sweepOuterW, sweepOuter, hL, ite_true, hne, hmod]
      exact sweepW_carry H W B hB inner F (q / 2) (lvl + 1) F g _ _ hstep hb2 hF hF (by omega)

theorem finishW_eq (W B : Nat) (hB : B < W) (inner : Nat → α) (F fo : Nat) :
    ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → c ≤ 2 ^ B → q ≠ 0 →
    (absFrom inner lvl q).length ≤ fs → (absFrom inner lvl q).length ≤ F →
    (absFrom inner lvl q).length < fo →
    finishW H W inner F fo c fs lvl =
      .ok (some (sweepOuter H inner F fo c (skipLow c fs lvl) (inner (skipLow c fs lvl)))) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hbound hq hfs hF hfo
    have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul hq) (by omega)
    have hbit : bitClear c lvl = decide (q % 2 = 0) := by rw [hc, bitClear_mul]
    have hold := absFrom_pos inner lvl q hq
    by_cases hodd : q % 2 = 1
    · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
      simp only [hodd, ite_true] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        simp only [finishW, skipLowW, skipLow, bitClearW, hL, ite_true, hstop, Except.bind,
          Bool.false_eq_true, ite_false]
        rw [sweepW_top H W B hB inner F q lvl fo _ c hc hbound hodd (by omega) (by omega)]
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        have := ih (q / 2) (by omega) (lvl + 1) f c hc' hbound (by omega) (by omega) (by omega)
          (by omega)
        simp only [finishW, skipLowW, skipLow, bitClearW, hL, ite_true, hclear] at this ⊢
        exact this

section
variable [DecidableEq α] [Inhabited α]

/-- **The width theorem.** With a `W`-bit counter and at most `2^(W-1)` leaves,
no shift by `W` or more is evaluated, the counter never wraps, and the result
is the root of the unbounded model, hence the tree's root. For the source,
`W = 32`: at most 2^31 leaves. -/
theorem rootW_eq (W : Nat) (hW : 0 < W) (l : List α) (hl : l.length ≤ 2 ^ (W - 1)) :
    rootW H W l = .ok (root H l) := by
  rw [← rootLit_eq_root]
  have hBW : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by decide) (by omega)
  match l, hl with
  | [], _ => rfl
  | a :: t, hl =>
    obtain ⟨_, _, h3⟩ := runLeaves_spec H (a :: t) (start : Lit α)
    have hcnt : (runLeaves H start (a :: t)).count = (a :: t).length := by
      rw [h3]; simp [start]
    have hlen := length_absFrom_le (runLeaves H start (a :: t)).inner
      (runLeaves H start (a :: t)).count 0
    have hrun := runLeavesW_eq H W (a :: t) (start : Lit α) (by simp only [start]; omega)
    have hf := finishW_eq H W (W - 1) (by omega) (runLeaves H start (a :: t)).inner
      ((runLeaves H start (a :: t)).count + 1) ((runLeaves H start (a :: t)).count + 1)
      (runLeaves H start (a :: t)).count 0 ((runLeaves H start (a :: t)).count + 1)
      (runLeaves H start (a :: t)).count (by simp) (by rw [hcnt]; exact hl)
      (by rw [hcnt]; simp) (by omega) (by omega) (by omega)
    simp only [rootW, hrun, rootLit]
    change finishW H W _ _ _ _ _ 0 = _
    rw [hf]

end

/-! ## Above `2^(W-1)` leaves it does fault: small widths, by evaluation -/

/-- An arbitrary combining function on numbers, for the examples. -/
def exampleH (a b : Nat) : Nat := (a * 31 + b * 17 + 7) % 1000003

/-- Four bits: eight leaves are fine. -/
example : rootW exampleH 4 (List.range 8) = .ok (root exampleH (List.range 8)) :=
  rootW_eq exampleH 4 (by decide) _ (by decide)

/-- Whether the `W`-bit computation hits a shift by `W` or more on `n` leaves. -/
def faults (W n : Nat) : Bool :=
  match rootW exampleH W (List.range n) with
  | .error .shift => true
  | _ => false

/-- Every leaf count from `2^(W-1) + 1` to `2^W + 3` faults, for each width
from 1 to 6: checked one count at a time by evaluation. Together with
`rootW_eq` this pins the limit at exactly `2^(W-1)` for these widths; the
general statement is `rootW_fault` in `MerkleWidthExact`. -/
example : ((List.range' 2 4).all (faults 1) && (List.range' 3 5).all (faults 2) &&
    (List.range' 5 7).all (faults 3) && (List.range' 9 11).all (faults 4) &&
    (List.range' 17 19).all (faults 5) && (List.range' 33 35).all (faults 6)) = true := by
  decide

section
variable [DecidableEq α] [Inhabited α]

/-- The mutation flag with a `W`-bit counter. It is settled in the leaf phase,
before the sweep raises the counter. -/
def mutatedW (W : Nat) (l : List α) : Except Fault Bool :=
  (runLeavesW H W start l).map (·.mutated)

/-- With fewer than `2^W` leaves the flag is computed without a fault and has
its tree-level meaning. (The root needs the smaller bound `2^(W-1)`.) -/
theorem mutatedW_eq (W : Nat) (l : List α) (hl : l.length < 2 ^ W) :
    mutatedW H W l = .ok (mutatedTree H l) := by
  rw [← mutatedLit_eq_mutatedTree]
  simp [mutatedW, runLeavesW_eq H W l (start : Lit α) (by simp only [start]; omega),
    mutatedLit, Except.map]

end

end Bsv.Merkle
