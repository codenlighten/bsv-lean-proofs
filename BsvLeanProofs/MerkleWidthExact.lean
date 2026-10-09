import BsvLeanProofs.MerkleWidth

/-!
# The width bound is exact

`MerkleWidth.rootW_eq` shows the `W`-bit computation is right for at most
`2^(W-1)` leaves. This file proves the converse: with more leaves it always
reaches a shift by `W` or more. So the root computation succeeds exactly when
the list has at most `2^(W-1)` leaves; for the source's 32 bits, 2^31.

How it fails: between `2^(W-1)` and `2^W` leaves the final sweep raises the
counter to `2^W`, which wraps to zero, after which every bit test passes until
the level reaches `W`. With `2^W` leaves or more the counter already wraps to
zero in the leaf phase, with the same effect.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

theorem bitClear_zero (l : Nat) : bitClear 0 l = true := by
  simp [bitClear]

theorem le_two_pow_pred (W : Nat) (hW : 0 < W) : W ≤ 2 ^ (W - 1) := by
  have := Nat.lt_two_pow_self (n := W - 1)
  omega

/-- With the counter at zero the sweep's inner loop climbs to level `W`. -/
theorem sweepInnerW_zero (W : Nat) (inner : Nat → α) : ∀ (fuel lvl : Nat) (h : α),
    lvl ≤ W → W - lvl < fuel → sweepInnerW H W inner 0 fuel lvl h = .error .shift
  | 0, _, _, _, hf => by omega
  | f + 1, lvl, h, hle, hf => by
    by_cases hl : lvl < W
    · simp only [sweepInnerW, bitClearW, hl, ite_true, bitClear_zero]
      exact sweepInnerW_zero W inner f (lvl + 1) _ (by omega) (by omega)
    · simp [sweepInnerW, bitClearW, hl]

section
variable [DecidableEq α]

/-- The same for the leaf loop. -/
theorem leafCarryW_zero (W : Nat) (inner : Nat → α) : ∀ (fuel lvl : Nat) (h : α) (m : Bool),
    lvl ≤ W → W - lvl < fuel → leafCarryW H W inner 0 fuel lvl h m = .error .shift
  | 0, _, _, _, _, hf => by omega
  | f + 1, lvl, h, m, hle, hf => by
    by_cases hl : lvl < W
    · simp only [leafCarryW, bitClearW, hl, ite_true, bitClear_zero]
      exact leafCarryW_zero W inner f (lvl + 1) _ _ (by omega) (by omega)
    · simp [leafCarryW, bitClearW, hl]

end

/-- Above `2^(W-1)` the sweep cannot stop: the counter is never a power of two
below `2^W`, so it is raised until it wraps. -/
theorem sweepW_carry_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F : Nat) (hF0 : W < F) :
    ∀ (p L fi fo : Nat) (h : α) (cc : Nat),
    cc = (p + 1) * 2 ^ L → 2 ^ (W - 1) < cc → cc < 2 ^ W →
    (absFrom inner L p).length < fi → (absFrom inner L p).length < F →
    (absFrom inner L p).length < fo →
    (sweepInnerW H W inner cc fi L h).bind (fun r => sweepOuterW H W inner F fo cc r.1 r.2) =
      .error .shift := by
  have hpow : 2 ^ W = 2 * 2 ^ (W - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h cc hcc hlow hhigh hfi hF hfo
    have hL : L < W := level_lt_of_pow_le (c := cc) (by rw [hcc]; exact pow_le_mul (by omega))
      hhigh
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      match fo, hfo with
      | 0, hfo => omega
      | g + 1, hfo =>
        by_cases hodd : p % 2 = 1
        · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
          have hold := absFrom_pos inner L p (by omega)
          simp only [hodd, ite_true] at hold
          have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
            congr 1; omega
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          simp only [sweepInnerW, bitClearW, hL, ite_true, hclear]
          exact ih (p / 2) (by omega) (L + 1) f (g + 1) _ cc hcc' hlow hhigh (by omega)
            (by omega) (by omega)
        · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
          have hp : p ≠ 0 := by
            intro hp0
            subst hp0
            have h1 : cc = 2 ^ L := by rw [hcc]; simp
            have h2 : 2 ^ L ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          have hold := absFrom_pos inner L p hp
          simp only [hodd, ite_false] at hold
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          have e1 : sweepInnerW H W inner cc (f + 1) L h = .ok (L, h) := by
            simp [sweepInnerW, bitClearW, hL, hstop]
          have hne : (cc != 1 <<< L) = true := by
            rw [hcc, ne_one_shiftLeft]; simp; omega
          have hstep : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
            congr 1; omega
          have hb2 : cc + 1 <<< L ≤ 2 ^ W := by
            rw [hcc, add_one_shiftLeft]
            exact sweep_bound (by rw [← hcc]; omega) (by omega) hp
          have hpos : 0 < 1 <<< L := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos L
          rw [e1]
          change sweepOuterW H W inner F (g + 1) cc L h = .error .shift
          by_cases hwrap : cc + 1 <<< L = 2 ^ W
          · have hmod : (cc + 1 <<< L) % 2 ^ W = 0 := by rw [hwrap]; simp
            simp only [sweepOuterW, hL, ite_true, hne, hmod]
            rw [sweepInnerW_zero H W inner F (L + 1) _ (by omega) (by omega)]
            rfl
          · have hlt : cc + 1 <<< L < 2 ^ W := by omega
            have hmod : (cc + 1 <<< L) % 2 ^ W = cc + 1 <<< L := Nat.mod_eq_of_lt hlt
            simp only [sweepOuterW, hL, ite_true, hne, hmod]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ hstep (by omega) hlt (by omega)
              (by omega) (by omega)

theorem sweepW_top_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F : Nat) (hF0 : W < F)
    (q lvl fo : Nat) (h : α) (c : Nat) (hc : c = q * 2 ^ lvl)
    (hlow : 2 ^ (W - 1) < c) (hhigh : c < 2 ^ W) (hodd : q % 2 = 1)
    (hF : (absFrom inner (lvl + 1) (q / 2)).length < F)
    (hfo : (absFrom inner (lvl + 1) (q / 2)).length + 1 < fo) :
    sweepOuterW H W inner F fo c lvl h = .error .shift := by
  have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul (by omega))
    hhigh
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    have hq : q ≠ 1 := by
      intro hq1
      subst hq1
      have h1 : c = 2 ^ lvl := by rw [hc]; simp
      have h2 : 2 ^ lvl ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
    have hstep : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
      rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
      congr 1; omega
    have hb2 : c + 1 <<< lvl ≤ 2 ^ W := by
      rw [hc, add_one_shiftLeft]
      have : (q - 1 + 1) * 2 ^ lvl ≤ 2 ^ W := by
        have e : q - 1 + 1 = q := by omega
        rw [e, ← hc]; omega
      have := sweep_bound this (by omega) (by omega)
      have e : q - 1 + 2 = q + 1 := by omega
      rwa [e] at this
    have hpos : 0 < 1 <<< lvl := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos lvl
    by_cases hwrap : c + 1 <<< lvl = 2 ^ W
    · have hmod : (c + 1 <<< lvl) % 2 ^ W = 0 := by rw [hwrap]; simp
      simp only [sweepOuterW, hL, ite_true, hne, hmod]
      rw [sweepInnerW_zero H W inner F (lvl + 1) _ (by omega) (by omega)]
      rfl
    · have hlt : c + 1 <<< lvl < 2 ^ W := by omega
      have hmod : (c + 1 <<< lvl) % 2 ^ W = c + 1 <<< lvl := Nat.mod_eq_of_lt hlt
      simp only [sweepOuterW, hL, ite_true, hne, hmod]
      exact sweepW_carry_fault H W hW inner F hF0 (q / 2) (lvl + 1) F g _ _ hstep (by omega) hlt
        hF hF (by omega)

theorem finishW_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F fo : Nat) (hF0 : W < F) :
    ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → 2 ^ (W - 1) < c → c < 2 ^ W → q ≠ 0 →
    (absFrom inner lvl q).length ≤ fs → (absFrom inner lvl q).length ≤ F →
    (absFrom inner lvl q).length < fo →
    finishW H W inner F fo c fs lvl = .error .shift := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hlow hhigh hq hfs hF hfo
    have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul hq) hhigh
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
        simp only [finishW, skipLowW, bitClearW, hL, ite_true, hstop, Except.bind]
        rw [sweepW_top_fault H W hW inner F hF0 q lvl fo _ c hc hlow hhigh hodd (by omega)
          (by omega)]
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        have := ih (q / 2) (by omega) (lvl + 1) f c hc' hlow hhigh (by omega) (by omega)
          (by omega) (by omega)
        simp only [finishW, skipLowW, bitClearW, hL, ite_true, hclear] at this ⊢
        exact this

section
variable [DecidableEq α] [Inhabited α]

/-- Reaching `2^W` leaves faults in the leaf phase. -/
theorem runLeavesW_fault (W : Nat) (hW : 0 < W) : ∀ (l : List α) (s : Lit α),
    s.count < 2 ^ W → 2 ^ W ≤ s.count + l.length →
    runLeavesW H W s l = .error .shift
  | [], s, h1, h2 => by simp at h2; omega
  | a :: t, s, h1, h2 => by
    simp only [List.length_cons] at h2
    by_cases hlast : s.count + 1 = 2 ^ W
    · have hmod : (s.count + 1) % 2 ^ W = 0 := by rw [hlast]; simp
      have hWlt : W < 2 ^ W := Nat.lt_two_pow_self
      have := leafCarryW_zero H W s.inner (s.count + 1) 0 a s.mutated (by omega) (by omega)
      simp [runLeavesW, addLeafW, hmod, this]
    · have h3 := (addLeaf_spec H s a).2.2
      simp only [runLeavesW, addLeafW_eq H W s a (by omega)]
      exact runLeavesW_fault W hW t (addLeaf H s a) (by rw [h3]; omega) (by rw [h3]; omega)

/-- With more than `2^(W-1)` leaves the root computation faults. -/
theorem rootW_fault (W : Nat) (hW : 0 < W) (l : List α) (hl : 2 ^ (W - 1) < l.length) :
    rootW H W l = .error .shift := by
  have hWle := le_two_pow_pred W hW
  match l, hl with
  | [], hl => simp at hl
  | a :: t, hl =>
    by_cases hbig : 2 ^ W ≤ (a :: t).length
    · have := runLeavesW_fault H W hW (a :: t) (start : Lit α)
        (by simp only [start]; exact Nat.two_pow_pos W) (by simp only [start]; omega)
      simp [rootW, this, Except.bind]
    · have hlt : (a :: t).length < 2 ^ W := by omega
      obtain ⟨_, _, h3⟩ := runLeaves_spec H (a :: t) (start : Lit α)
      have hcnt : (runLeaves H start (a :: t)).count = (a :: t).length := by
        rw [h3]; simp [start]
      have hlen := length_absFrom_le (runLeaves H start (a :: t)).inner
        (runLeaves H start (a :: t)).count 0
      have hrun := runLeavesW_eq H W (a :: t) (start : Lit α) (by simp only [start]; omega)
      have hf := finishW_fault H W hW (runLeaves H start (a :: t)).inner
        ((runLeaves H start (a :: t)).count + 1) ((runLeaves H start (a :: t)).count + 1)
        (by omega) (runLeaves H start (a :: t)).count 0
        ((runLeaves H start (a :: t)).count + 1) (runLeaves H start (a :: t)).count (by simp)
        (by rw [hcnt]; exact hl) (by rw [hcnt]; exact hlt) (by rw [hcnt]; simp) (by omega)
        (by omega) (by omega)
      simp only [rootW, hrun]
      change finishW H W _ _ _ _ _ 0 = _
      rw [hf]

/-- **The bound is exact.** The `W`-bit root computation succeeds if and only
if the list has at most `2^(W-1)` leaves. For the source, `W = 32`: 2^31. -/
theorem rootW_ok_iff (W : Nat) (hW : 0 < W) (l : List α) :
    (∃ r, rootW H W l = .ok r) ↔ l.length ≤ 2 ^ (W - 1) := by
  constructor
  · intro ⟨r, hr⟩
    apply Nat.le_of_not_lt
    intro hlt
    rw [rootW_fault H W hW l hlt] at hr
    cases hr
  · intro hle
    exact ⟨_, rootW_eq H W hW l hle⟩

end

end Bsv.Merkle
