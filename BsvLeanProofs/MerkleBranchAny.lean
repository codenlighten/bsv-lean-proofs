import BsvLeanProofs.MerkleLiteralBranch

/-!
# The constant-space branch at any position

`MerkleBranch0` and `MerkleLiteralBranch` treat position 0. This file treats
every position.

What is modelled: as in `MerkleLiteralBranch`, the branch logic of
`MerkleComputation` with its own variables, for a requested position `pos`.
What is proved: for `pos` inside the list, the pushes are the siblings on the
path from leaf `pos` to the root, where a node paired with itself contributes
itself (`branchSelf`).
What differs from the source: step budgets and an unbounded counter.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-! ## Marked leaves on the slot model -/

/-- Slots after adding marked leaves. -/
def cntSM : List (α × Bool) → List (Slot α) → List (Slot α)
  | [], s => s
  | (h, m) :: t, s => cntSM t (insS H h m s)

def cntPM : List (α × Bool) → List (Slot α) → List α
  | [], _ => []
  | (h, m) :: t, s => insP H h m s ++ cntPM t (insS H h m s)

/-- The branch for the marked leaf, as the slot model emits it. -/
def branchCSM (l : List (α × Bool)) : List α :=
  cntPM H l [] ++ finishB H (cntSM H l [])

def pairsM : List (α × Bool) → List (α × Bool)
  | (a, ma) :: (b, mb) :: t => (H a b, mb || ma) :: pairsM t
  | _ => []

def oddM : List (α × Bool) → Option (α × Bool)
  | [] => none
  | [x] => some x
  | _ :: _ :: t => oddM t

/-- What the complete pairs of a level push. -/
def levelPush : List (α × Bool) → List α
  | (a, ma) :: (b, mb) :: t => push a ma b mb ++ levelPush t
  | _ => []

def noMarks (l : List (α × Bool)) : Bool := l.all (fun x => !x.2)

def noMarksS : List (Slot α) → Bool
  | [] => true
  | none :: s => noMarksS s
  | some (_, m) :: s => !m && noMarksS s

/-- At most one leaf is marked. -/
def atMostOne : List (α × Bool) → Bool
  | [] => true
  | (_, m) :: t => if m then noMarks t else atMostOne t

/-- One level up, keeping the mark. -/
def levelM : List (α × Bool) → List (α × Bool)
  | [] => []
  | [(z, mz)] => [(H z z, mz)]
  | (a, ma) :: (b, mb) :: t => (H a b, mb || ma) :: levelM t

theorem length_levelM : ∀ l : List (α × Bool), (levelM H l).length = (l.length + 1) / 2
  | [] => by simp [levelM]
  | [(_, _)] => by simp [levelM]
  | (_, _) :: (_, _) :: t => by simp only [levelM, List.length_cons, length_levelM t]; omega

/-- What the marked node pushes when it is the unpaired last node. -/
def selfPush (l : List (α × Bool)) : List α :=
  match oddM l with
  | some (z, true) => [z]
  | _ => []

/-- The branch of the marked leaf on the tree: at each level the pair's push,
or the node itself when the marked node is the unpaired last one. -/
def branchM : List (α × Bool) → List α
  | [] => []
  | [_] => []
  | a :: b :: t =>
    levelPush (a :: b :: t) ++ selfPush (a :: b :: t) ++ branchM (levelM H (a :: b :: t))
termination_by l => l.length
decreasing_by simp only [length_levelM, List.length_cons]; omega

/-! ### Small facts -/

theorem levelM_eq : ∀ l : List (α × Bool),
    levelM H l = pairsM H l ++ (match oddM l with | none => [] | some (z, mz) => [(H z z, mz)])
  | [] => by simp [levelM, pairsM, oddM]
  | [(_, _)] => by simp [levelM, pairsM, oddM]
  | (_, _) :: (_, _) :: t => by simp [levelM, pairsM, oddM, levelM_eq t]

theorem insP_noMark (h : α) : ∀ s : List (Slot α), noMarksS s = true → insP H h false s = []
  | [], _ => rfl
  | none :: _, _ => rfl
  | some (x, mx) :: s, hs => by
    simp only [noMarksS, Bool.and_eq_true, Bool.not_eq_true'] at hs
    simp [insP, push, hs.1, insP_noMark (H x h) s hs.2]

theorem insS_noMark (h : α) : ∀ s : List (Slot α), noMarksS s = true →
    noMarksS (insS H h false s) = true
  | [], _ => by simp [insS, noMarksS]
  | none :: s, hs => by simpa [insS, noMarksS] using hs
  | some (x, mx) :: s, hs => by
    simp only [noMarksS, Bool.and_eq_true, Bool.not_eq_true'] at hs
    simp [insS, noMarksS, hs.1, insS_noMark (H x h) s hs.2]

theorem cntPM_noMarks : ∀ (l : List (α × Bool)) (s : List (Slot α)),
    noMarks l = true → noMarksS s = true → cntPM H l s = []
  | [], _, _, _ => rfl
  | (h, m) :: t, s, hl, hs => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hm, ht⟩ := hl
    subst hm
    simp [cntPM, insP_noMark H h s hs, cntPM_noMarks t _ (by simpa [noMarks] using ht)
      (insS_noMark H h s hs)]

theorem levelPush_noMarks : ∀ l : List (α × Bool), noMarks l = true → levelPush l = []
  | [], _ => rfl
  | [_], _ => rfl
  | (a, ma) :: (b, mb) :: t, hl => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hma, hmb, ht⟩ := hl
    subst hma; subst hmb
    simp [levelPush, push, levelPush_noMarks t (by simpa [noMarks] using ht)]

theorem noMarks_pairsM : ∀ l : List (α × Bool), noMarks l = true → noMarks (pairsM H l) = true
  | [], _ => rfl
  | [_], _ => rfl
  | (a, ma) :: (b, mb) :: t, hl => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hma, hmb, ht⟩ := hl
    subst hma; subst hmb
    have := noMarks_pairsM t (by simpa [noMarks] using ht)
    simpa [pairsM, noMarks] using this

theorem noMarks_levelM : ∀ l : List (α × Bool), noMarks l = true → noMarks (levelM H l) = true
  | [], _ => rfl
  | [(z, mz)], hl => by simpa [levelM, noMarks] using hl
  | (a, ma) :: (b, mb) :: t, hl => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hma, hmb, ht⟩ := hl
    subst hma; subst hmb
    have := noMarks_levelM t (by simpa [noMarks] using ht)
    simpa [levelM, noMarks] using this

theorem atMostOne_of_noMarks : ∀ l : List (α × Bool), noMarks l = true → atMostOne l = true
  | [], _ => rfl
  | (a, m) :: t, hl => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨hm, ht⟩ := hl
    subst hm
    simpa [atMostOne] using atMostOne_of_noMarks t (by simpa [noMarks] using ht)

theorem atMostOne_levelM : ∀ l : List (α × Bool), atMostOne l = true →
    atMostOne (levelM H l) = true
  | [], _ => rfl
  | [(z, mz)], _ => by cases mz <;> simp [levelM, atMostOne, noMarks]
  | (a, ma) :: (b, mb) :: t, hl => by
    cases ma <;> cases mb <;> simp [atMostOne, noMarks] at hl
    · simpa [levelM, atMostOne] using atMostOne_levelM t hl
    · have := noMarks_levelM H t (by simpa [noMarks] using hl)
      simpa [levelM, atMostOne] using this
    · have := noMarks_levelM H t (by simpa [noMarks] using hl)
      simpa [levelM, atMostOne] using this

theorem oddM_unmarked : ∀ (l : List (α × Bool)) (z : α) (m : Bool), noMarks l = true →
    oddM l = some (z, m) → m = false
  | [], _, _, _, h => by simp [oddM] at h
  | [(x, mx)], z, m, hl, h => by
    simp only [oddM, Option.some.injEq, Prod.mk.injEq] at h
    simp only [noMarks, List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true'] at hl
    rw [← h.2]; exact hl
  | _ :: _ :: t, z, m, hl, h => by
    simp only [noMarks, List.all_cons, Bool.and_eq_true] at hl
    exact oddM_unmarked t z m (by simpa [noMarks] using hl.2.2) (by simpa [oddM] using h)

/-- If the unpaired last node is the marked one, no pair is marked. -/
theorem noMarks_pairsM_of_odd_marked : ∀ (l : List (α × Bool)) (z : α), atMostOne l = true →
    oddM l = some (z, true) → noMarks (pairsM H l) = true
  | [], _, _, h => by simp [oddM] at h
  | [_], _, _, _ => rfl
  | (a, ma) :: (b, mb) :: t, z, hl, h => by
    have ht : oddM t = some (z, true) := by simpa [oddM] using h
    cases ma <;> cases mb <;> simp [atMostOne, noMarks] at hl
    · have := noMarks_pairsM_of_odd_marked t z hl ht
      simpa [pairsM, noMarks] using this
    · have := oddM_unmarked t z true (by simpa [noMarks] using hl) ht
      simp at this
    · have := oddM_unmarked t z true (by simpa [noMarks] using hl) ht
      simp at this

/-! ### The slot model emits the tree's branch -/

/-- Adding a level's leaves to a counter whose lowest slot is free: the pairs
go one level up, and the pushes are this level's followed by the upper
levels'. Needs: no mark at all in the leaves, or no mark in the slots and at
most one in the leaves. -/
theorem cnt_none_M : ∀ (l : List (α × Bool)) (s : List (Slot α)),
    (noMarks l = true ∨ (noMarksS s = true ∧ atMostOne l = true)) →
    cntSM H l (none :: s) = oddM l :: cntSM H (pairsM H l) s ∧
    cntPM H l (none :: s) = levelPush l ++ cntPM H (pairsM H l) s
  | [], _, _ => by simp [cntSM, cntPM, oddM, pairsM, levelPush]
  | [(_, _)], _, _ => by simp [cntSM, cntPM, insS, insP, oddM, pairsM, levelPush]
  | (a, ma) :: (b, mb) :: t, s, hyp => by
    have hnext : noMarks t = true ∨
        (noMarksS (insS H (H a b) (mb || ma) s) = true ∧ atMostOne t = true) := by
      rcases hyp with hl | ⟨hs, hl⟩
      · left
        simp only [noMarks, List.all_cons, Bool.and_eq_true] at hl
        simpa [noMarks] using hl.2.2
      · cases ma <;> cases mb <;> simp [atMostOne, noMarks] at hl
        · right; exact ⟨by simpa using insS_noMark H (H a b) s hs, hl⟩
        · left; simpa [noMarks] using hl
        · left; simpa [noMarks] using hl
    have hcomm : insP H (H a b) (mb || ma) s ++ levelPush t =
        levelPush t ++ insP H (H a b) (mb || ma) s := by
      rcases hyp with hl | ⟨hs, hl⟩
      · simp only [noMarks, List.all_cons, Bool.and_eq_true] at hl
        simp [levelPush_noMarks t (by simpa [noMarks] using hl.2.2)]
      · cases ma <;> cases mb <;> simp [atMostOne, noMarks] at hl
        · simp [insP_noMark H (H a b) s hs]
        · simp [levelPush_noMarks t (by simpa [noMarks] using hl)]
        · simp [levelPush_noMarks t (by simpa [noMarks] using hl)]
    obtain ⟨i1, i2⟩ := cnt_none_M t (insS H (H a b) (mb || ma) s) hnext
    refine ⟨?_, ?_⟩
    · simp only [cntSM, insS, pairsM, oddM, i1]
    · simp only [cntPM, insS, insP, pairsM, levelPush, i2, List.nil_append, List.append_assoc]
      rw [← List.append_assoc (insP H (H a b) (mb || ma) s), hcomm, List.append_assoc]

theorem cnt_nil_M (a b : α × Bool) (t : List (α × Bool))
    (hl : atMostOne (a :: b :: t) = true) :
    cntSM H (a :: b :: t) [] = oddM (a :: b :: t) :: cntSM H (pairsM H (a :: b :: t)) [] ∧
    cntPM H (a :: b :: t) [] = levelPush (a :: b :: t) ++ cntPM H (pairsM H (a :: b :: t)) [] := by
  obtain ⟨a, ma⟩ := a
  obtain ⟨b, mb⟩ := b
  have hnext : noMarks t = true ∨
      (noMarksS (insS H (H a b) (mb || ma) []) = true ∧ atMostOne t = true) := by
    cases ma <;> cases mb <;> simp [atMostOne, noMarks] at hl
    · right; exact ⟨by simp [insS, noMarksS], hl⟩
    · left; simpa [noMarks] using hl
    · left; simpa [noMarks] using hl
  obtain ⟨i1, i2⟩ := cnt_none_M H t (insS H (H a b) (mb || ma) []) hnext
  refine ⟨?_, ?_⟩
  · simp only [cntSM, insS, pairsM, oddM] at i1 ⊢
    exact i1
  · simp only [cntPM, insS, insP, pairsM, levelPush, List.nil_append, List.append_nil,
      List.append_assoc] at i2 ⊢
    rw [i2]

theorem cntSM_append : ∀ (p : List (α × Bool)) (h : α) (m : Bool) (s : List (Slot α)),
    cntSM H (p ++ [(h, m)]) s = insS H h m (cntSM H p s)
  | [], _, _, _ => rfl
  | (_, _) :: p, h, m, s => by simp [cntSM, cntSM_append p h m]

theorem cntPM_append : ∀ (p : List (α × Bool)) (h : α) (m : Bool) (s : List (Slot α)),
    cntPM H (p ++ [(h, m)]) s = cntPM H p s ++ insP H h m (cntSM H p s)
  | [], _, _, _ => by simp [cntPM, cntSM]
  | (_, _) :: p, h, m, s => by simp [cntPM, cntSM, cntPM_append p h m]

theorem cntSM_any : ∀ (l : List (α × Bool)) (s : List (Slot α)),
    s.any Option.isSome = true → (cntSM H l s).any Option.isSome = true
  | [], _, h => h
  | (a, m) :: t, s, _ => cntSM_any t _ (insS_any H a m s)

/-- **The slot model's branch for the marked leaf is the tree's.** -/
theorem branchCSM_eq_branchM (l : List (α × Bool)) (hl : atMostOne l = true) :
    branchCSM H l = branchM H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn, hl with
    | [], _, _ => simp [branchCSM, cntPM, cntSM, finishB, branchM]
    | [(a, m)], _, _ => simp [branchCSM, cntPM, cntSM, insS, insP, finishB, topB, branchM]
    | a :: b :: t, hn, hl =>
      obtain ⟨c1, c2⟩ := cnt_nil_M H a b t hl
      have hlev := levelM_eq H (a :: b :: t)
      have hlen := length_levelM H (a :: b :: t)
      have hone := atMostOne_levelM H (a :: b :: t) hl
      have ihl := ih _ (by subst hn; rw [hlen]; simp only [List.length_cons]; omega)
        (levelM H (a :: b :: t)) hone rfl
      rw [branchM, ← ihl]
      simp only [branchCSM, c1, c2]
      cases ho : oddM (a :: b :: t) with
      | none =>
        rw [ho] at hlev
        simp only [List.append_nil] at hlev
        simp [selfPush, ho, finishB, hlev, branchCSM, List.append_assoc]
      | some zm =>
        obtain ⟨z, mz⟩ := zm
        rw [ho] at hlev
        have hne : (cntSM H (pairsM H (a :: b :: t)) []).all Option.isNone = false := by
          obtain ⟨a, ma⟩ := a
          obtain ⟨b, mb⟩ := b
          exact not_all_none_of_any_some' _ (by
            simp only [pairsM, cntSM]
            exact cntSM_any H _ _ (insS_any H _ _ _))
        have hsp : selfPush (a :: b :: t) = (if mz then [z] else []) := by
          cases mz <;> simp [selfPush, ho]
        have hcomm : cntPM H (pairsM H (a :: b :: t)) [] ++ (if mz then [z] else []) =
            (if mz then [z] else []) ++ cntPM H (pairsM H (a :: b :: t)) [] := by
          cases hmz : mz
          · simp
          · have := noMarks_pairsM_of_odd_marked H (a :: b :: t) z hl (by rw [ho, hmz])
            simp [cntPM_noMarks H _ [] this (by simp [noMarksS])]
        simp only [finishB, topB, hne, Bool.false_eq_true, ite_false, carryB_eq, hsp, hlev,
          branchCSM, cntSM_append, cntPM_append, List.append_assoc]
        rw [← List.append_assoc (cntPM H (pairsM H (a :: b :: t)) []), hcomm,
          List.append_assoc]

/-! ## The literal computation at any position -/

/-- Leaves numbered from `k`, marked when their number is `pos`. -/
def markFrom (k pos : Nat) : List α → List (α × Bool)
  | [] => []
  | a :: t => (a, k == pos) :: markFrom (k + 1) pos t

/-- With no `matchlevel` set and an unmatched leaf, the loop never matches. -/
theorem leafCarryB_unmatched (inner : Nat → α) (c : Nat) : ∀ (fuel lvl : Nat) (h : α)
    (acc : List α), (leafCarryB H inner none c fuel lvl h false acc).2.2.1 = false
  | 0, _, _, _ => rfl
  | f + 1, lvl, h, acc => by
    by_cases hb : bitClear c lvl = true
    · simp only [leafCarryB, hb, ite_true, isMark]
      simpa using leafCarryB_unmatched inner c f (lvl + 1) (H (inner lvl) h) acc
    · simp [leafCarryB, hb]

theorem runLeavesB_gen (pos : Nat) : ∀ (l : List α) (s : LitB α),
    markOK s.ml 0 s.count → (s.count ≤ pos → s.ml = none) →
    absB (runLeavesB H pos s l).inner (runLeavesB H pos s l).ml 0 (runLeavesB H pos s l).count =
        cntSM H (markFrom s.count pos l) (absB s.inner s.ml 0 s.count) ∧
    (runLeavesB H pos s l).branch =
        s.branch ++ cntPM H (markFrom s.count pos l) (absB s.inner s.ml 0 s.count) ∧
    (runLeavesB H pos s l).count = s.count + l.length
  | [], s, _, _ => by simp [runLeavesB, markFrom, cntSM, cntPM]
  | a :: t, s, hok, hnone => by
    obtain ⟨h1, h2, h3, h4⟩ := addLeafB_spec H pos s a hok
      (fun hm => hnone (by have : s.count = pos := by simpa using hm
                           omega))
    have hnone' : (addLeafB H pos s a).count ≤ pos → (addLeafB H pos s a).ml = none := by
      intro hle
      rw [h3] at hle
      have hml : s.ml = none := hnone (by omega)
      have hne : (s.count == pos) = false := by simp; omega
      have hr := leafCarryB_unmatched H s.inner (s.count + 1) (s.count + 1) 0 a []
      show newMark s.ml (leafCarryB H s.inner s.ml (s.count + 1) (s.count + 1) 0 a
        (s.count == pos) []) = none
      rw [hml, hne]
      simp [newMark, hr]
    obtain ⟨g1, g2, g3⟩ := runLeavesB_gen pos t (addLeafB H pos s a) h4 hnone'
    have e : runLeavesB H pos s (a :: t) = runLeavesB H pos (addLeafB H pos s a) t := rfl
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, h1, h3]; rfl
    · rw [g2, h2, h1, h3]; simp [markFrom, cntPM, List.append_assoc]
    · rw [g3, h3]; simp only [List.length_cons]; omega

section
variable [Inhabited α]

/-- The literal branch for position `pos` is the slot model's branch for the
list with leaf `pos` marked. -/
theorem branchLit_eq_branchCSM (pos : Nat) (l : List α) :
    branchLit H pos l = branchCSM H (markFrom 0 pos l) := by
  match l with
  | [] => simp [branchLit, branchCSM, markFrom, cntPM, cntSM, finishB]
  | a :: t =>
    have hok0 : markOK (startB : LitB α).ml 0 (startB : LitB α).count := by
      intro k hk; simp [startB] at hk
    obtain ⟨g1, g2, g3⟩ := runLeavesB_gen H pos (a :: t) (startB : LitB α) hok0 (fun _ => rfl)
    have habs0 : absB (startB : LitB α).inner (startB : LitB α).ml 0 (startB : LitB α).count = [] := by
      simp [startB, absB_zero]
    have hbr0 : (startB : LitB α).branch = [] := rfl
    have hc0 : (startB : LitB α).count = 0 := rfl
    rw [habs0, hc0] at g1 g2
    rw [hbr0] at g2
    rw [hc0] at g3
    have hcount : (runLeavesB H pos startB (a :: t)).count ≠ 0 := by
      rw [g3]; simp
    have hlen := length_absB_le (runLeavesB H pos startB (a :: t)).inner
      (runLeavesB H pos startB (a :: t)).ml (runLeavesB H pos startB (a :: t)).count 0
    simp only [branchLit]
    rw [sweepB_finish H _ _ _ _ _ _ 0 _ _ (by simp) hcount (by omega) (by omega) (by omega),
      g1, g2]
    simp [branchCSM]

end

/-! ## The tree's branch by index -/

theorem xor_one (j : Nat) : j ^^^ 1 = if j % 2 = 0 then j + 1 else j - 1 := by
  have hd : (j ^^^ 1) / 2 = j / 2 := by rw [Nat.xor_div_two]; simp
  have hm : (j ^^^ 1) % 2 = 1 ↔ ¬ (j % 2 = 1 ↔ 1 % 2 = 1) := Nat.xor_mod_two_eq_one
  by_cases h : j % 2 = 0
  · have : (j ^^^ 1) % 2 = 1 := hm.mpr (by omega)
    simp only [h, ite_true]; omega
  · have : ¬ (j ^^^ 1) % 2 = 1 := fun hx => (hm.mp hx) (by omega)
    simp only [h, ite_false]; omega

/-- The sibling of position `i` in a level, or the node itself when it is the
unpaired last one. -/
def sibOrSelf (l : List α) (i : Nat) : List α :=
  match l[i ^^^ 1]? with
  | some s => [s]
  | none => match l[i]? with
    | some x => [x]
    | none => []

/-- The branch of leaf `i` on the tree, with a self-pairing written as the
node itself (what `MerkleComputation` pushes). -/
def branchSelf : List α → Nat → List α
  | [], _ => []
  | [_], _ => []
  | a :: b :: t, i => sibOrSelf (a :: b :: t) i ++ branchSelf (level H (a :: b :: t)) (i / 2)
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

def unm (l : List α) : List (α × Bool) := l.map (·, false)

/-- The list with the leaf at index `i` marked. -/
def markAt : Nat → List α → List (α × Bool)
  | _, [] => []
  | 0, a :: t => (a, true) :: unm t
  | i + 1, a :: t => (a, false) :: markAt i t

theorem noMarks_unm (l : List α) : noMarks (unm l) = true := by
  simp [noMarks, unm]

theorem atMostOne_markAt : ∀ (i : Nat) (l : List α), atMostOne (markAt i l) = true
  | _, [] => by simp [markAt, atMostOne]
  | 0, a :: t => by simp [markAt, atMostOne, noMarks_unm]
  | i + 1, a :: t => by simpa [markAt, atMostOne] using atMostOne_markAt i t

theorem markFrom_gt : ∀ (l : List α) (k pos : Nat), pos < k → markFrom k pos l = unm l
  | [], _, _, _ => rfl
  | a :: t, k, pos, h => by
    have : (k == pos) = false := by simp; omega
    simp [markFrom, unm, this, markFrom_gt t (k + 1) pos (by omega)]

theorem markFrom_le : ∀ (l : List α) (k pos : Nat), k ≤ pos →
    markFrom k pos l = markAt (pos - k) l
  | [], _, _, _ => by simp [markFrom, markAt]
  | a :: t, k, pos, h => by
    by_cases hk : k = pos
    · subst hk
      simp [markFrom, markAt, markFrom_gt t (k + 1) k (by omega)]
    · have hne : (k == pos) = false := by simp [hk]
      obtain ⟨j, hj⟩ : ∃ j, pos - k = j + 1 := ⟨pos - k - 1, by omega⟩
      have : pos - (k + 1) = j := by omega
      simp [markFrom, hne, hj, markAt, markFrom_le t (k + 1) pos (by omega), this]

theorem levelM_unm : ∀ l : List α, levelM H (unm l) = unm (level H l)
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have := levelM_unm t
    simp only [unm, List.map_cons, levelM, level] at this ⊢
    simp [this]

theorem selfPush_noMarks (l : List (α × Bool)) (h : noMarks l = true) : selfPush l = [] := by
  unfold selfPush
  cases ho : oddM l with
  | none => rfl
  | some zm =>
    obtain ⟨z, m⟩ := zm
    have := oddM_unmarked l z m h ho
    subst this
    rfl

/-- One level of the marked list: what is pushed, and the next level. -/
theorem level_markAt : ∀ (l : List α) (i : Nat), i < l.length →
    levelPush (markAt i l) ++ selfPush (markAt i l) = sibOrSelf l i ∧
    levelM H (markAt i l) = markAt (i / 2) (level H l)
  | [], _, h => by simp at h
  | [a], i, h => by
    have : i = 0 := by simpa using h
    subst this
    simp [markAt, unm, levelPush, selfPush, oddM, sibOrSelf, levelM, level]
  | a :: b :: t, 0, _ => by
    refine ⟨?_, ?_⟩
    · simp [markAt, unm, levelPush, push, sibOrSelf, selfPush, oddM]
      have h1 := levelPush_noMarks (unm t) (noMarks_unm t)
      have h2 := selfPush_noMarks (unm t) (noMarks_unm t)
      simp only [unm, selfPush] at h1 h2
      simp [h1, h2]
    · have := levelM_unm H t
      simp only [unm] at this
      simp [markAt, unm, levelM, level, this]
  | a :: b :: t, 1, _ => by
    refine ⟨?_, ?_⟩
    · simp [markAt, unm, levelPush, push, sibOrSelf, selfPush, oddM]
      have h1 := levelPush_noMarks (unm t) (noMarks_unm t)
      have h2 := selfPush_noMarks (unm t) (noMarks_unm t)
      simp only [unm, selfPush] at h1 h2
      simp [h1, h2]
    · have := levelM_unm H t
      simp only [unm] at this
      simp [markAt, unm, levelM, level, this]
  | a :: b :: t, j + 2, h => by
    have hj : j < t.length := by simpa using h
    obtain ⟨i1, i2⟩ := level_markAt t j hj
    have hx : (j + 2) ^^^ 1 = (j ^^^ 1) + 2 := by
      rw [xor_one, xor_one]
      by_cases hm : j % 2 = 0
      · have : (j + 2) % 2 = 0 := by omega
        simp [hm, this]
      · have : ¬ (j + 2) % 2 = 0 := by omega
        simp only [hm, this, ite_false]; omega
    refine ⟨?_, ?_⟩
    · have hs : sibOrSelf (a :: b :: t) (j + 2) = sibOrSelf t j := by
        simp [sibOrSelf, hx]
      rw [hs, ← i1]
      simp [markAt, levelPush, push, selfPush, oddM]
    · have hd : (j + 2) / 2 = j / 2 + 1 := by omega
      simp [markAt, levelM, level, i2, hd]

/-- The branch of the marked leaf is the branch by index. -/
theorem branchM_markAt (l : List α) (i : Nat) (hi : i < l.length) :
    branchM H (markAt i l) = branchSelf H l i := by
  induction hn : l.length using Nat.strongRecOn generalizing l i with
  | _ n ih =>
    match l, hn, hi with
    | [], _, hi => simp at hi
    | [a], _, hi =>
      have : i = 0 := by simpa using hi
      subst this
      simp [markAt, unm, branchM, branchSelf]
    | a :: b :: t, hn, hi =>
      obtain ⟨l1, l2⟩ := level_markAt H (a :: b :: t) i hi
      have hlen := length_level H (a :: b :: t)
      have hshape : ∃ x y r, markAt i (a :: b :: t) = x :: y :: r := by
        match i with
        | 0 => exact ⟨_, _, _, rfl⟩
        | 1 => exact ⟨_, _, _, rfl⟩
        | j + 2 => exact ⟨_, _, _, rfl⟩
      obtain ⟨x, y, r, hxy⟩ := hshape
      rw [branchSelf, ← l1]
      rw [hxy] at l1 l2 ⊢
      rw [branchM, l2]
      congr 1
      exact ih _ (by subst hn; rw [hlen]; simp only [List.length_cons]; omega) _ _
        (by rw [hlen]; simp only [List.length_cons] at hi ⊢; omega) rfl

section
variable [Inhabited α]

/-- **The literal computation's branch at any position inside the list is the
tree's branch of that leaf.** -/
theorem branchLit_eq_branchSelf (l : List α) (i : Nat) (hi : i < l.length) :
    branchLit H i l = branchSelf H l i := by
  rw [branchLit_eq_branchCSM, markFrom_le l 0 i (Nat.zero_le _), Nat.sub_zero,
    branchCSM_eq_branchM H _ (atMostOne_markAt i l), branchM_markAt H l i hi]

end

end Bsv.Merkle
