import BsvLeanProofs.MerkleLiteral
import BsvLeanProofs.MerkleBranch0

/-!
# The literal branch output for position 0 refines the marked-slot model

`MerkleBranch0` reads the source's `match_level` as a mark on one slot. This
file removes that assumption for position 0: it models the branch logic of
`MerkleComputation` with its own variables (`matchlevel` as an optional level,
`matchh` as a flag, the array `inner`, the counter `count`) and proves that
the pushes are those of `branchCS0`, hence the tree's branch of the first leaf.

What is modelled: the two `if (matchh) … else if (matchlevel == level) …`
blocks, the push before a self-combine in the sweep, and
`if (matchh) matchlevel = level` after a leaf. The requested position is a
parameter; the theorem is for position 0.
What differs from the source: step budgets and an unbounded counter, as in
`MerkleLiteral`.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-- `matchlevel == level`. -/
def isMark (ml : Option Nat) (level : Nat) : Bool := decide (ml = some level)

/-- Marked slots from level `lvl` upward for an (`inner`, `matchlevel`, count) triple. -/
def absB (inner : Nat → α) (ml : Option Nat) (lvl q : Nat) : List (Slot α) :=
  if h : q = 0 then []
  else (if q % 2 = 1 then some (inner lvl, isMark ml lvl) else none) ::
    absB inner ml (lvl + 1) (q / 2)
termination_by q
decreasing_by omega

theorem absB_zero (inner : Nat → α) (ml : Option Nat) (lvl : Nat) : absB inner ml lvl 0 = [] := by
  rw [absB]; simp

theorem absB_pos (inner : Nat → α) (ml : Option Nat) (lvl q : Nat) (h : q ≠ 0) :
    absB inner ml lvl q =
      (if q % 2 = 1 then some (inner lvl, isMark ml lvl) else none) ::
        absB inner ml (lvl + 1) (q / 2) := by
  rw [absB]; simp [h]

theorem absB_congr (f g : Nat → α) (m1 m2 : Option Nat) : ∀ (q lvl : Nat),
    (∀ k, lvl ≤ k → f k = g k ∧ isMark m1 k = isMark m2 k) →
    absB f m1 lvl q = absB g m2 lvl q := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl hfg
    by_cases hq : q = 0
    · subst hq; rw [absB_zero, absB_zero]
    · rw [absB_pos f m1 lvl q hq, absB_pos g m2 lvl q hq, (hfg lvl (Nat.le_refl _)).1,
        (hfg lvl (Nat.le_refl _)).2,
        ih (q / 2) (by omega) (lvl + 1) (fun k hk => hfg k (by omega))]

theorem length_absB_le (inner : Nat → α) (ml : Option Nat) : ∀ (q lvl : Nat),
    (absB inner ml lvl q).length ≤ q := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl
    by_cases hq : q = 0
    · subst hq; rw [absB_zero]; simp
    · rw [absB_pos inner ml lvl q hq]
      have := ih (q / 2) (by omega) (lvl + 1)
      simp only [List.length_cons]
      omega

theorem absB_not_all_none (inner : Nat → α) (ml : Option Nat) : ∀ (q lvl : Nat), q ≠ 0 →
    (absB inner ml lvl q).all Option.isNone = false := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl hq
    rw [absB_pos inner ml lvl q hq]
    by_cases hodd : q % 2 = 1
    · simp [hodd]
    · have := ih (q / 2) (by omega) (lvl + 1) (by omega)
      simp [hodd, this]

/-- A set `matchlevel` at or above `lvl` points at an occupied slot. -/
def markOK (ml : Option Nat) (lvl q : Nat) : Prop :=
  ∀ k, ml = some k → lvl ≤ k → q / 2 ^ (k - lvl) % 2 = 1

theorem markOK_succ {ml : Option Nat} {lvl q : Nat} (h : markOK ml lvl q) :
    markOK ml (lvl + 1) (q / 2) := by
  intro k hk hle
  have := h k hk (by omega)
  have e : k - lvl = (k - (lvl + 1)) + 1 := by omega
  rw [e, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at this
  exact this

/-! ## Adding a leaf -/

/-- The leaf-phase loop with the branch logic: level, hash, `matchh`, pushes. -/
def leafCarryB (inner : Nat → α) (ml : Option Nat) (count : Nat) :
    Nat → Nat → α → Bool → List α → Nat × α × Bool × List α
  | 0, level, h, m, acc => (level, h, m, acc)
  | fuel + 1, level, h, m, acc =>
    if bitClear count level then
      if m then
        leafCarryB inner ml count fuel (level + 1) (H (inner level) h) true (acc ++ [inner level])
      else if isMark ml level then
        leafCarryB inner ml count fuel (level + 1) (H (inner level) h) true (acc ++ [h])
      else
        leafCarryB inner ml count fuel (level + 1) (H (inner level) h) false acc
    else (level, h, m, acc)

/-- `matchlevel` after the leaf: `if (matchh) matchlevel = level`. -/
def newMark (ml : Option Nat) (r : Nat × α × Bool × List α) : Option Nat :=
  if r.2.2.1 then some r.1 else ml

theorem leafCarryB_step (inner : Nat → α) (ml : Option Nat) (c f lvl : Nat) (h : α) (m : Bool)
    (acc : List α) (hclear : bitClear c lvl = true) :
    leafCarryB H inner ml c (f + 1) lvl h m acc =
      leafCarryB H inner ml c f (lvl + 1) (H (inner lvl) h) (m || isMark ml lvl)
        (acc ++ push (inner lvl) (isMark ml lvl) h m) := by
  cases m <;> cases hk : isMark ml lvl <;> simp [leafCarryB, hclear, hk, push]

theorem div_pow_succ_of_even (q j : Nat) (h : q % 2 = 0) :
    (q + 1) / 2 ^ (j + 1) = q / 2 ^ (j + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1; omega

theorem leafCarryB_spec (inner : Nat → α) (ml : Option Nat) (c : Nat) :
    ∀ (q lvl fuel : Nat) (h : α) (m : Bool) (acc : List α),
    c / 2 ^ lvl = q + 1 → (absB inner ml lvl q).length < fuel →
    markOK ml lvl q → (m = true → ∀ k, lvl ≤ k → ml ≠ some k) →
    absB (upd inner (leafCarryB H inner ml c fuel lvl h m acc).1
          (leafCarryB H inner ml c fuel lvl h m acc).2.1)
        (newMark ml (leafCarryB H inner ml c fuel lvl h m acc)) lvl (q + 1) =
      insS H h m (absB inner ml lvl q) ∧
    (leafCarryB H inner ml c fuel lvl h m acc).2.2.2 = acc ++ insP H h m (absB inner ml lvl q) ∧
    lvl ≤ (leafCarryB H inner ml c fuel lvl h m acc).1 ∧
    (m = true → (leafCarryB H inner ml c fuel lvl h m acc).2.2.1 = true) ∧
    markOK (newMark ml (leafCarryB H inner ml c fuel lvl h m acc)) lvl (q + 1) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fuel h m acc hc hfuel hok hm
    match fuel, hfuel with
    | 0, hfuel => omega
    | f + 1, hfuel =>
      have hbit : bitClear c lvl = decide ((q + 1) % 2 = 0) := by rw [bitClear_eq, hc]
      by_cases hodd : q % 2 = 1
      · have hq : q ≠ 0 := by omega
        have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
        have hc' : c / 2 ^ (lvl + 1) = q / 2 + 1 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hc]; omega
        have hold := absB_pos inner ml lvl q hq
        simp only [hodd, ite_true] at hold
        have hlen : (absB inner ml (lvl + 1) (q / 2)).length < f := by
          rw [hold] at hfuel; simpa using hfuel
        have hm2 : (m || isMark ml lvl) = true → ∀ k, lvl + 1 ≤ k → ml ≠ some k := by
          intro h2 k hk
          cases hmm : m
          · have : isMark ml lvl = true := by simpa [hmm] using h2
            have : ml = some lvl := by simpa [isMark] using this
            rw [this]; intro he; injection he with he; omega
          · exact hm hmm k (by omega)
        rw [leafCarryB_step H inner ml c f lvl h m acc hclear]
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih (q / 2) (by omega) (lvl + 1) f (H (inner lvl) h)
          (m || isMark ml lvl) (acc ++ push (inner lvl) (isMark ml lvl) h m) hc' hlen
          (markOK_succ hok) hm2
        have hd : (q + 1) / 2 = q / 2 + 1 := by omega
        refine ⟨?_, ?_, by omega, ?_, ?_⟩
        · rw [absB_pos _ _ lvl (q + 1) (by omega), hold]
          have he : ¬ (q + 1) % 2 = 1 := by omega
          simp only [he, ite_false, hd, insS, h1]
        · rw [h2, hold]; simp [insP, List.append_assoc]
        · intro hmt; exact h4 (by simp [hmt])
        · intro k hk hle
          by_cases hkl : k = lvl
          · exfalso
            subst hkl
            simp only [newMark] at hk
            split at hk
            · injection hk with hk; omega
            · rename_i hnm
              have : isMark ml k = true := by simp [isMark, hk]
              exact hnm (h4 (by simp [this]))
          · have := h5 k hk (by omega)
            have e : k - lvl = (k - (lvl + 1)) + 1 := by omega
            rw [e, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, hd]
            exact this
      · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
        have hres : leafCarryB H inner ml c (f + 1) lvl h m acc = (lvl, h, m, acc) := by
          simp [leafCarryB, hstop]
        rw [hres]
        have hnomark : m = false → isMark ml lvl = false := by
          intro _
          cases hk : isMark ml lvl
          · rfl
          · exfalso
            have : ml = some lvl := by simpa [isMark] using hk
            have := hok lvl this (Nat.le_refl _)
            simp at this; omega
        have hmark : isMark (newMark ml (lvl, h, m, acc)) lvl = m := by
          cases hmm : m
          · simp [newMark, hnomark hmm]
          · simp [newMark, isMark]
        have hd : (q + 1) / 2 = q / 2 := by omega
        have ho : (q + 1) % 2 = 1 := by omega
        have hcg : absB (upd inner lvl h) (newMark ml (lvl, h, m, acc)) (lvl + 1) (q / 2) =
            absB inner ml (lvl + 1) (q / 2) := by
          apply absB_congr
          intro k hk
          refine ⟨by simp [upd]; omega, ?_⟩
          cases hmm : m
          · simp [newMark]
          · have h1 : isMark ml k = false := by
              have := hm hmm k (by omega)
              simp [isMark, this]
            have h2 : isMark (some lvl) k = false := by
              simp [isMark]; omega
            simp [newMark, h1, h2]
        refine ⟨?_, ?_, Nat.le_refl _, fun hmt => hmt, ?_⟩
        · rw [absB_pos _ _ lvl (q + 1) (by omega)]
          simp only [ho, ite_true, hd, hcg, hmark]
          by_cases hq : q = 0
          · subst hq; simp [absB_zero, insS, upd]
          · rw [absB_pos inner ml lvl q hq]; simp [hodd, insS, upd]
        · by_cases hq : q = 0
          · subst hq; simp [absB_zero, insP]
          · rw [absB_pos inner ml lvl q hq]; simp [hodd, insP]
        · intro k hk hle
          by_cases hkl : k = lvl
          · subst hkl; simp; omega
          · have hmf : m = false := by
              cases hmm : m
              · rfl
              · exfalso; simp [newMark, hmm] at hk; omega
            have hk' : ml = some k := by simpa [newMark, hmf] using hk
            have := hok k hk' hle
            obtain ⟨j, hj⟩ : ∃ j, k - lvl = j + 1 := ⟨k - lvl - 1, by omega⟩
            rw [hj] at this ⊢
            rw [div_pow_succ_of_even q j (by omega)]
            exact this

/-- The state of the leaf phase with the branch variables. -/
structure LitB (α : Type) where
  inner : Nat → α
  count : Nat
  ml : Option Nat
  branch : List α

/-- One round of the leaf loop for requested position `pos`:
`matchh = (count == branchpos)` is taken before `count++`. -/
def addLeafB (pos : Nat) (s : LitB α) (leaf : α) : LitB α :=
  let c := s.count + 1
  let r := leafCarryB H s.inner s.ml c c 0 leaf (s.count == pos) []
  { inner := upd s.inner r.1 r.2.1, count := c, ml := newMark s.ml r,
    branch := s.branch ++ r.2.2.2 }

def runLeavesB (pos : Nat) (s : LitB α) (l : List α) : LitB α := l.foldl (addLeafB H pos) s

theorem addLeafB_spec (pos : Nat) (s : LitB α) (leaf : α) (hok : markOK s.ml 0 s.count)
    (hm : (s.count == pos) = true → s.ml = none) :
    absB (addLeafB H pos s leaf).inner (addLeafB H pos s leaf).ml 0 (addLeafB H pos s leaf).count =
        insS H leaf (s.count == pos) (absB s.inner s.ml 0 s.count) ∧
    (addLeafB H pos s leaf).branch =
        s.branch ++ insP H leaf (s.count == pos) (absB s.inner s.ml 0 s.count) ∧
    (addLeafB H pos s leaf).count = s.count + 1 ∧
    markOK (addLeafB H pos s leaf).ml 0 (addLeafB H pos s leaf).count := by
  have hlen := length_absB_le s.inner s.ml s.count 0
  obtain ⟨h1, h2, _, _, h5⟩ := leafCarryB_spec H s.inner s.ml (s.count + 1) s.count 0
    (s.count + 1) leaf (s.count == pos) [] (by simp) (by omega) hok
    (fun hmt k _ => by rw [hm hmt]; simp)
  refine ⟨h1, ?_, rfl, h5⟩
  simp only [addLeafB, h2, List.nil_append]

/-- Leaves after the requested one: none of them matches. -/
theorem runLeavesB_spec (pos : Nat) : ∀ (l : List α) (s : LitB α),
    pos < s.count → markOK s.ml 0 s.count →
    absB (runLeavesB H pos s l).inner (runLeavesB H pos s l).ml 0 (runLeavesB H pos s l).count =
        cntS H l (absB s.inner s.ml 0 s.count) ∧
    (runLeavesB H pos s l).branch = s.branch ++ cntP H l (absB s.inner s.ml 0 s.count) ∧
    (runLeavesB H pos s l).count = s.count + l.length
  | [], s, _, _ => by simp [runLeavesB, cntS, cntP]
  | a :: t, s, hpos, hok => by
    have hne : (s.count == pos) = false := by simp; omega
    obtain ⟨h1, h2, h3, h4⟩ := addLeafB_spec H pos s a hok (by simp [hne])
    rw [hne] at h1 h2
    obtain ⟨g1, g2, g3⟩ := runLeavesB_spec pos t (addLeafB H pos s a) (by rw [h3]; omega) h4
    have e : runLeavesB H pos s (a :: t) = runLeavesB H pos (addLeafB H pos s a) t := rfl
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, h1]; rfl
    · rw [g2, h2, h1]; simp [cntP, List.append_assoc]
    · rw [g3, h3]; simp only [List.length_cons]; omega

/-! ## The final sweep -/

/-- The outer loop of the sweep with its pushes. Its inner loop is the same
text as the leaf loop's, so `leafCarryB` is reused. -/
def sweepOuterB (inner : Nat → α) (ml : Option Nat) (F : Nat) :
    Nat → Nat → Nat → α → Bool → List α → List α
  | 0, _, _, _, _, acc => acc
  | fuel + 1, count, level, h, m, acc =>
    if count != 1 <<< level then
      let r := leafCarryB H inner ml (count + 1 <<< level) F (level + 1) (H h h) m
        (if m then acc ++ [h] else acc)
      sweepOuterB inner ml F fuel (count + 1 <<< level) r.1 r.2.1 r.2.2.1 r.2.2.2
    else acc

theorem sweepB_carry (inner : Nat → α) (ml : Option Nat) (F : Nat) :
    ∀ (p L fi fo : Nat) (h : α) (m : Bool) (acc : List α) (cc : Nat),
    cc = (p + 1) * 2 ^ L →
    (absB inner ml L p).length < fi → (absB inner ml L p).length < F →
    (absB inner ml L p).length ≤ fo →
    sweepOuterB H inner ml F fo cc (leafCarryB H inner ml cc fi L h m acc).1
        (leafCarryB H inner ml cc fi L h m acc).2.1 (leafCarryB H inner ml cc fi L h m acc).2.2.1
        (leafCarryB H inner ml cc fi L h m acc).2.2.2 =
      acc ++ carryB H h m (absB inner ml L p) := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h m acc cc hcc hfi hF hfo
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      by_cases hp : p = 0
      · subst hp
        have hstop : bitClear cc L = false := by rw [hbit]; simp
        have hres : leafCarryB H inner ml cc (f + 1) L h m acc = (L, h, m, acc) := by
          simp [leafCarryB, hstop]
        rw [hres, absB_zero]
        match fo with
        | 0 => simp [sweepOuterB, carryB]
        | g + 1 =>
          have hne : (cc != 1 <<< L) = false := by rw [hcc, ne_one_shiftLeft]; simp
          simp [sweepOuterB, hne, carryB]
      · have hold := absB_pos inner ml L p hp
        by_cases hodd : p % 2 = 1
        · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
          simp only [hodd, ite_true] at hold
          have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
            congr 1; omega
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          rw [leafCarryB_step H inner ml cc f L h m acc hclear, hold,
            ih (p / 2) (by omega) (L + 1) f fo _ _ _ cc hcc' (by omega) (by omega) (by omega)]
          simp [carryB, List.append_assoc]
        · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
          have hres : leafCarryB H inner ml cc (f + 1) L h m acc = (L, h, m, acc) := by
            simp [leafCarryB, hstop]
          simp only [hodd, ite_false] at hold
          have hrest : (absB inner ml (L + 1) (p / 2)).all Option.isNone = false :=
            absB_not_all_none inner ml _ _ (by omega)
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          rw [hres, hold]
          match fo, hfo with
          | 0, hfo => omega
          | g + 1, hfo =>
            have hne : (cc != 1 <<< L) = true := by
              rw [hcc, ne_one_shiftLeft]; simp; omega
            have hcc' : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
              congr 1; omega
            simp only [sweepOuterB, hne, ite_true]
            rw [ih (p / 2) (by omega) (L + 1) F g _ _ _ _ hcc' (by omega) (by omega) (by omega)]
            cases m <;> simp [carryB, hrest, List.append_assoc]

theorem sweepB_top (inner : Nat → α) (ml : Option Nat) (F : Nat) (q lvl fo : Nat) (h : α)
    (m : Bool) (acc : List α) (c : Nat) (hc : c = q * 2 ^ lvl) (hodd : q % 2 = 1)
    (hF : (absB inner ml (lvl + 1) (q / 2)).length < F)
    (hfo : (absB inner ml (lvl + 1) (q / 2)).length < fo) :
    sweepOuterB H inner ml F fo c lvl h m acc =
      acc ++ topB H h m (absB inner ml (lvl + 1) (q / 2)) := by
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    by_cases hq : q = 1
    · subst hq
      have hne : (c != 1 <<< lvl) = false := by rw [hc, ne_one_shiftLeft]; simp
      simp [sweepOuterB, hne, topB, absB_zero]
    · have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
      have hrest : (absB inner ml (lvl + 1) (q / 2)).all Option.isNone = false :=
        absB_not_all_none inner ml _ _ (by omega)
      have hcc' : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
        rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
        congr 1; omega
      simp only [sweepOuterB, hne, ite_true]
      rw [sweepB_carry H inner ml F (q / 2) (lvl + 1) F g _ _ _ _ hcc' hF hF (by omega)]
      cases m <;> simp [topB, hrest, List.append_assoc]

theorem sweepB_finish (inner : Nat → α) (ml : Option Nat) (F fo : Nat) (acc : List α) :
    ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → q ≠ 0 →
    (absB inner ml lvl q).length ≤ fs → (absB inner ml lvl q).length ≤ F →
    (absB inner ml lvl q).length ≤ fo →
    sweepOuterB H inner ml F fo c (skipLow c fs lvl) (inner (skipLow c fs lvl))
        (isMark ml (skipLow c fs lvl)) acc =
      acc ++ finishB H (absB inner ml lvl q) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hq hfs hF hfo
    have hbit : bitClear c lvl = decide (q % 2 = 0) := by rw [hc, bitClear_mul]
    have hold := absB_pos inner ml lvl q hq
    by_cases hodd : q % 2 = 1
    · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
      have hskip : skipLow c fs lvl = lvl := by
        cases fs <;> simp [skipLow, hstop]
      simp only [hodd, ite_true] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      rw [hskip, hold, finishB]
      exact sweepB_top H inner ml F q lvl fo _ _ _ c hc hodd (by omega) (by omega)
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        rw [hold, finishB]
        simp only [skipLow, hclear, ite_true]
        exact ih (q / 2) (by omega) (lvl + 1) f c hc' (by omega) (by omega) (by omega) (by omega)

/-! ## The whole branch computation -/

section whole
variable [Inhabited α]

def startB : LitB α := { inner := fun _ => default, count := 0, ml := none, branch := [] }

/-- The branch of the leaf at `pos`, as the literal computation emits it. -/
def branchLit (pos : Nat) (l : List α) : List α :=
  match l with
  | [] => []
  | _ =>
    let s := runLeavesB H pos startB l
    let F := s.count + 1
    let level := skipLow s.count F 0
    sweepOuterB H s.inner s.ml F F s.count level (s.inner level) (isMark s.ml level) s.branch

/-- **The literal branch for position 0 is the tree's branch of the first leaf.** -/
theorem branchLit_zero (l : List α) : branchLit H 0 l = branch0 H l := by
  rw [← branchCS0_eq_branch0]
  match l with
  | [] => simp [branchLit, branchCS0]
  | a :: t =>
    have hok0 : markOK (startB : LitB α).ml 0 (startB : LitB α).count := by
      intro k hk; simp [startB] at hk
    obtain ⟨h1, h2, h3, h4⟩ := addLeafB_spec H 0 (startB : LitB α) a hok0 (by simp [startB])
    have hs : ((startB : LitB α).count == 0) = true := by simp [startB]
    have habs0 : absB (startB : LitB α).inner (startB : LitB α).ml 0 (startB : LitB α).count = [] := by
      simp [startB, absB_zero]
    have hbr0 : (startB : LitB α).branch = [] := rfl
    have hc0 : (startB : LitB α).count = 0 := rfl
    rw [hs, habs0] at h1 h2
    rw [hbr0] at h2
    rw [hc0] at h3
    obtain ⟨g1, g2, g3⟩ := runLeavesB_spec H 0 t (addLeafB H 0 startB a) (by rw [h3]; omega) h4
    have e : runLeavesB H 0 startB (a :: t) = runLeavesB H 0 (addLeafB H 0 startB a) t := rfl
    have hcount : (runLeavesB H 0 startB (a :: t)).count ≠ 0 := by rw [e, g3, h3]; omega
    have hlen := length_absB_le (runLeavesB H 0 startB (a :: t)).inner
      (runLeavesB H 0 startB (a :: t)).ml (runLeavesB H 0 startB (a :: t)).count 0
    simp only [branchLit]
    rw [sweepB_finish H _ _ _ _ _ _ 0 _ _ (by simp) hcount (by omega) (by omega) (by omega),
      e, g1, g2, h1, h2]
    simp [branchCS0, insP]

/-- **End to end, on the literal computation.** Folding any replacement first
leaf `x` through the branch the literal computation emits for position 0 of
`y :: t` gives the root the literal computation returns for `x :: t`. -/
theorem fold_branchLit_zero [DecidableEq α] (x y : α) (t : List α) :
    some (fold H x ((branchLit H 0 (y :: t)).map some) 0) = rootLit H (x :: t) := by
  rw [branchLit_zero, ← branch_zero, fold_branch_zero, rootLit_eq_root]

end whole

end Bsv.Merkle
