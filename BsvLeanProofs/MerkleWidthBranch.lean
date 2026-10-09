import BsvLeanProofs.MerkleWidth
import BsvLeanProofs.MerkleBranchAny

/-!
# The counter width and the branch output

`MerkleWidth` proves the width bound for the root. This file does the same for
the branch: with a `W`-bit counter and at most `2^(W-1)` leaves, the branch
computation evaluates no shift by `W` or more, its counter never wraps, and it
emits the tree's branch of the requested leaf.

What is modelled: the branch logic of `MerkleLiteralBranch`, with the checks of
`MerkleWidth` (fault on `1 << level` with `level ≥ W`; counter reduced modulo
`2^W` after each addition).
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

def leafCarryBW (W : Nat) (inner : Nat → α) (ml : Option Nat) (count : Nat) :
    Nat → Nat → α → Bool → List α → Except Fault (Nat × α × Bool × List α)
  | 0, _, _, _, _ => .error .fuel
  | fuel + 1, level, h, m, acc =>
    match bitClearW W count level with
    | .error e => .error e
    | .ok true =>
      if m then
        leafCarryBW W inner ml count fuel (level + 1) (H (inner level) h) true (acc ++ [inner level])
      else if isMark ml level then
        leafCarryBW W inner ml count fuel (level + 1) (H (inner level) h) true (acc ++ [h])
      else
        leafCarryBW W inner ml count fuel (level + 1) (H (inner level) h) false acc
    | .ok false => .ok (level, h, m, acc)

theorem leafCarryBW_step (W : Nat) (inner : Nat → α) (ml : Option Nat) (c f lvl : Nat) (h : α)
    (m : Bool) (acc : List α) (hlvl : lvl < W) (hclear : bitClear c lvl = true) :
    leafCarryBW H W inner ml c (f + 1) lvl h m acc =
      leafCarryBW H W inner ml c f (lvl + 1) (H (inner lvl) h) (m || isMark ml lvl)
        (acc ++ push (inner lvl) (isMark ml lvl) h m) := by
  cases m <;> cases hk : isMark ml lvl <;>
    simp [leafCarryBW, bitClearW, hlvl, hclear, hk, push]

theorem leafCarryBW_eq (W : Nat) (inner : Nat → α) (ml : Option Nat) (c : Nat)
    (hc : c < 2 ^ W) : ∀ (q lvl fuel : Nat) (h : α) (m : Bool) (acc : List α),
    c / 2 ^ lvl = q + 1 → (absB inner ml lvl q).length < fuel →
    leafCarryBW H W inner ml c fuel lvl h m acc = .ok (leafCarryB H inner ml c fuel lvl h m acc) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fuel h m acc hq hfuel
    match fuel, hfuel with
    | 0, hfuel => omega
    | f + 1, hfuel =>
      have hlvl : lvl < W := level_lt_of_pow_le (pow_le_of_div_pos hq) hc
      have hbit : bitClear c lvl = decide ((q + 1) % 2 = 0) := by rw [bitClear_eq, hq]
      by_cases hodd : q % 2 = 1
      · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
        have hq' : c / 2 ^ (lvl + 1) = q / 2 + 1 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hq]; omega
        have hold := absB_pos inner ml lvl q (by omega)
        simp only [hodd, ite_true] at hold
        have hlen : (absB inner ml (lvl + 1) (q / 2)).length < f := by
          rw [hold] at hfuel; simpa using hfuel
        rw [leafCarryBW_step H W inner ml c f lvl h m acc hlvl hclear,
          leafCarryB_step H inner ml c f lvl h m acc hclear]
        exact ih (q / 2) (by omega) (lvl + 1) f _ _ _ hq' hlen
      · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
        simp [leafCarryBW, leafCarryB, bitClearW, hlvl, hstop]

def addLeafBW (W pos : Nat) (s : LitB α) (leaf : α) : Except Fault (LitB α) :=
  let c := (s.count + 1) % 2 ^ W
  match leafCarryBW H W s.inner s.ml c (s.count + 1) 0 leaf (s.count == pos) [] with
  | .error e => .error e
  | .ok r => .ok { inner := upd s.inner r.1 r.2.1, count := c, ml := newMark s.ml r,
                   branch := s.branch ++ r.2.2.2 }

def runLeavesBW (W pos : Nat) : LitB α → List α → Except Fault (LitB α)
  | s, [] => .ok s
  | s, a :: t =>
    match addLeafBW H W pos s a with
    | .error e => .error e
    | .ok s' => runLeavesBW W pos s' t

theorem addLeafBW_eq (W pos : Nat) (s : LitB α) (leaf : α) (hc : s.count + 1 < 2 ^ W) :
    addLeafBW H W pos s leaf = .ok (addLeafB H pos s leaf) := by
  have hlen := length_absB_le s.inner s.ml s.count 0
  have hmod : (s.count + 1) % 2 ^ W = s.count + 1 := Nat.mod_eq_of_lt hc
  have := leafCarryBW_eq H W s.inner s.ml (s.count + 1) hc s.count 0 (s.count + 1) leaf
    (s.count == pos) [] (by simp) (by omega)
  simp only [addLeafBW, hmod, this, addLeafB]

theorem runLeavesBW_eq (W pos : Nat) : ∀ (l : List α) (s : LitB α),
    s.count + l.length < 2 ^ W → runLeavesBW H W pos s l = .ok (runLeavesB H pos s l)
  | [], s, _ => rfl
  | a :: t, s, hc => by
    simp only [List.length_cons] at hc
    have h3 : (addLeafB H pos s a).count = s.count + 1 := rfl
    simp only [runLeavesBW, addLeafBW_eq H W pos s a (by omega)]
    exact runLeavesBW_eq W pos t (addLeafB H pos s a) (by rw [h3]; omega)

def sweepOuterBW (W : Nat) (inner : Nat → α) (ml : Option Nat) (F : Nat) :
    Nat → Nat → Nat → α → Bool → List α → Except Fault (List α)
  | 0, _, _, _, _, _ => .error .fuel
  | fuel + 1, count, level, h, m, acc =>
    if level < W then
      if count != 1 <<< level then
        (leafCarryBW H W inner ml ((count + 1 <<< level) % 2 ^ W) F (level + 1) (H h h) m
            (if m then acc ++ [h] else acc)).bind
          fun r => sweepOuterBW W inner ml F fuel ((count + 1 <<< level) % 2 ^ W)
            r.1 r.2.1 r.2.2.1 r.2.2.2
      else .ok acc
    else .error .shift

theorem sweepBW_carry (W B : Nat) (hB : B < W) (inner : Nat → α) (ml : Option Nat) (F : Nat) :
    ∀ (p L fi fo : Nat) (h : α) (m : Bool) (acc : List α) (cc : Nat),
    cc = (p + 1) * 2 ^ L → cc ≤ 2 ^ B →
    (absB inner ml L p).length < fi → (absB inner ml L p).length < F →
    (absB inner ml L p).length < fo →
    (leafCarryBW H W inner ml cc fi L h m acc).bind
        (fun r => sweepOuterBW H W inner ml F fo cc r.1 r.2.1 r.2.2.1 r.2.2.2) =
      .ok (sweepOuterB H inner ml F fo cc (leafCarryB H inner ml cc fi L h m acc).1
        (leafCarryB H inner ml cc fi L h m acc).2.1 (leafCarryB H inner ml cc fi L h m acc).2.2.1
        (leafCarryB H inner ml cc fi L h m acc).2.2.2) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h m acc cc hcc hbound hfi hF hfo
    have hL : L < W := level_lt_of_pow_le (c := cc) (by rw [hcc]; exact pow_le_mul (by omega))
      (by omega)
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      match fo, hfo with
      | 0, hfo => omega
      | g + 1, hfo =>
        by_cases hodd : p % 2 = 1
        · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
          have hold := absB_pos inner ml L p (by omega)
          simp only [hodd, ite_true] at hold
          have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
            congr 1; omega
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          rw [leafCarryBW_step H W inner ml cc f L h m acc hL hclear,
            leafCarryB_step H inner ml cc f L h m acc hclear]
          exact ih (p / 2) (by omega) (L + 1) f (g + 1) _ _ _ cc hcc' hbound (by omega)
            (by omega) (by omega)
        · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
          have e1 : leafCarryBW H W inner ml cc (f + 1) L h m acc = .ok (L, h, m, acc) := by
            simp [leafCarryBW, bitClearW, hL, hstop]
          have e2 : leafCarryB H inner ml cc (f + 1) L h m acc = (L, h, m, acc) := by
            simp [leafCarryB, hstop]
          rw [e1, e2]
          change sweepOuterBW H W inner ml F (g + 1) cc L h m acc =
            .ok (sweepOuterB H inner ml F (g + 1) cc L h m acc)
          by_cases hp : p = 0
          · subst hp
            have hne : (cc != 1 <<< L) = false := by rw [hcc, ne_one_shiftLeft]; simp
            simp [sweepOuterBW, sweepOuterB, hL, hne]
          · have hold := absB_pos inner ml L p hp
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
            simp only [sweepOuterBW, sweepOuterB, hL, ite_true, hne, hmod]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ _ _ hstep hb2 (by omega) (by omega)
              (by omega)

theorem sweepBW_top (W B : Nat) (hB : B < W) (inner : Nat → α) (ml : Option Nat) (F : Nat)
    (q lvl fo : Nat) (h : α) (m : Bool) (acc : List α) (c : Nat) (hc : c = q * 2 ^ lvl)
    (hbound : c ≤ 2 ^ B) (hodd : q % 2 = 1)
    (hF : (absB inner ml (lvl + 1) (q / 2)).length < F)
    (hfo : (absB inner ml (lvl + 1) (q / 2)).length + 1 < fo) :
    sweepOuterBW H W inner ml F fo c lvl h m acc =
      .ok (sweepOuterB H inner ml F fo c lvl h m acc) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul (by omega))
    (by omega)
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    by_cases hq : q = 1
    · subst hq
      have hne : (c != 1 <<< lvl) = false := by rw [hc, ne_one_shiftLeft]; simp
      simp [sweepOuterBW, sweepOuterB, hL, hne]
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
      simp only [sweepOuterBW, sweepOuterB, hL, ite_true, hne, hmod]
      exact sweepBW_carry H W B hB inner ml F (q / 2) (lvl + 1) F g _ _ _ _ hstep hb2 hF hF
        (by omega)

/-- Find the lowest occupied level, then sweep, collecting the pushes. -/
def finishBW (W : Nat) (inner : Nat → α) (ml : Option Nat) (F fo count fs lvl : Nat)
    (acc : List α) : Except Fault (List α) :=
  (skipLowW W count fs lvl).bind fun level =>
    sweepOuterBW H W inner ml F fo count level (inner level) (isMark ml level) acc

theorem finishBW_eq (W B : Nat) (hB : B < W) (inner : Nat → α) (ml : Option Nat) (F fo : Nat)
    (acc : List α) : ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → c ≤ 2 ^ B → q ≠ 0 →
    (absB inner ml lvl q).length ≤ fs → (absB inner ml lvl q).length ≤ F →
    (absB inner ml lvl q).length < fo →
    finishBW H W inner ml F fo c fs lvl acc =
      .ok (sweepOuterB H inner ml F fo c (skipLow c fs lvl) (inner (skipLow c fs lvl))
        (isMark ml (skipLow c fs lvl)) acc) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hbound hq hfs hF hfo
    have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul hq) (by omega)
    have hbit : bitClear c lvl = decide (q % 2 = 0) := by rw [hc, bitClear_mul]
    have hold := absB_pos inner ml lvl q hq
    by_cases hodd : q % 2 = 1
    · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
      simp only [hodd, ite_true] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        simp only [finishBW, skipLowW, skipLow, bitClearW, hL, ite_true, hstop, Except.bind,
          Bool.false_eq_true, ite_false]
        exact sweepBW_top H W B hB inner ml F q lvl fo _ _ _ c hc hbound hodd (by omega)
          (by omega)
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
        simp only [finishBW, skipLowW, skipLow, bitClearW, hL, ite_true, hclear] at this ⊢
        exact this

section
variable [Inhabited α]

/-- The branch of leaf `pos` with a `W`-bit counter. -/
def branchW (W pos : Nat) (l : List α) : Except Fault (List α) :=
  match l with
  | [] => .ok []
  | _ =>
    (runLeavesBW H W pos startB l).bind fun s =>
      finishBW H W s.inner s.ml (s.count + 1) (s.count + 1) s.count (s.count + 1) 0 s.branch

/-- **The width theorem for the branch.** With a `W`-bit counter, at most
`2^(W-1)` leaves and a position inside the list, the branch computation raises
no error and emits the tree's branch of that leaf. For the source, `W = 32`. -/
theorem branchW_eq (W : Nat) (hW : 0 < W) (l : List α) (hl : l.length ≤ 2 ^ (W - 1))
    (i : Nat) (hi : i < l.length) : branchW H W i l = .ok (branchSelf H l i) := by
  rw [← branchLit_eq_branchSelf H l i hi]
  have hBW : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by decide) (by omega)
  match l, hl with
  | [], _ => rfl
  | a :: t, hl =>
    have hok0 : markOK (startB : LitB α).ml 0 (startB : LitB α).count := by
      intro k hk; simp [startB] at hk
    obtain ⟨_, _, g3⟩ := runLeavesB_gen H i (a :: t) (startB : LitB α) hok0 (fun _ => rfl)
    have hcnt : (runLeavesB H i startB (a :: t)).count = (a :: t).length := by
      rw [g3]; simp [startB]
    have hlen := length_absB_le (runLeavesB H i startB (a :: t)).inner
      (runLeavesB H i startB (a :: t)).ml (runLeavesB H i startB (a :: t)).count 0
    have hrun := runLeavesBW_eq H W i (a :: t) (startB : LitB α) (by simp only [startB]; omega)
    have hf := finishBW_eq H W (W - 1) (by omega) (runLeavesB H i startB (a :: t)).inner
      (runLeavesB H i startB (a :: t)).ml
      ((runLeavesB H i startB (a :: t)).count + 1) ((runLeavesB H i startB (a :: t)).count + 1)
      (runLeavesB H i startB (a :: t)).branch
      (runLeavesB H i startB (a :: t)).count 0 ((runLeavesB H i startB (a :: t)).count + 1)
      (runLeavesB H i startB (a :: t)).count (by simp) (by rw [hcnt]; exact hl)
      (by rw [hcnt]; simp) (by omega) (by omega) (by omega)
    simp only [branchW, hrun, branchLit]
    change finishBW H W _ _ _ _ _ _ 0 _ = _
    rw [hf]

end

end Bsv.Merkle
