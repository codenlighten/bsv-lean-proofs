import BsvLeanProofs.MerkleCounter

/-!
# The constant-space branch of the first leaf

`MerkleComputation` can also emit the branch of one leaf. It tracks, in
`match_level`, the level whose pending hash contains that leaf, and pushes a
sibling whenever that hash is combined.

What is modelled: the branch output for position 0, on the slot-list model of
`MerkleCounter`, with `match_level` stored as a mark on the slot it points to
(`some (h, true)`), and "this carried hash contains the leaf" as the flag `m`.
What is proved: for every non-empty list the pushes are exactly `branch0`, the
tree's branch of the first leaf.
What is assumed in this file: the slot-and-mark reading of `inner`, `count` and
`match_level`. `MerkleLiteralBranch` removes that assumption for position 0.
Other positions are not modelled here.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

abbrev Slot (α : Type) := Option (α × Bool)

/-- What one combine step pushes: the pending hash if the carried one holds the
leaf, the carried hash if the pending one does, otherwise nothing. -/
def push (x : α) (mx : Bool) (h : α) (m : Bool) : List α :=
  if m then [x] else if mx then [h] else []

/-- Slots after carrying `h` (flag `m`) up from the lowest level. -/
def insS (h : α) (m : Bool) : List (Slot α) → List (Slot α)
  | [] => [some (h, m)]
  | none :: s => some (h, m) :: s
  | some (x, mx) :: s => none :: insS (H x h) (m || mx) s

/-- Branch entries pushed while doing so. -/
def insP (h : α) (m : Bool) : List (Slot α) → List α
  | [] => []
  | none :: _ => []
  | some (x, mx) :: s => push x mx h m ++ insP (H x h) (m || mx) s

/-- Slots after adding the leaves of `l`, none of which is the tracked leaf. -/
def cntS : List α → List (Slot α) → List (Slot α)
  | [], s => s
  | h :: t, s => cntS t (insS H h false s)

def cntP : List α → List (Slot α) → List α
  | [], _ => []
  | h :: t, s => insP H h false s ++ cntP t (insS H h false s)

/-- Pushes of the inner loop of the final sweep. -/
def carryB (h : α) (m : Bool) : List (Slot α) → List α
  | [] => []
  | some (x, mx) :: s => push x mx h m ++ carryB (H x h) (m || mx) s
  | none :: s =>
    if s.all Option.isNone then [] else (if m then [h] else []) ++ carryB (H h h) m s

def topB (h : α) (m : Bool) (s : List (Slot α)) : List α :=
  if s.all Option.isNone then [] else (if m then [h] else []) ++ carryB H (H h h) m s

/-- Pushes of the final sweep. -/
def finishB : List (Slot α) → List α
  | [] => []
  | none :: s => finishB s
  | some (h, m) :: s => topB H h m s

/-- The branch of position 0 as the constant-space computation emits it. -/
def branchCS0 : List α → List α
  | [] => []
  | a :: t => cntP H t (insS H a true []) ++ finishB H (cntS H t (insS H a true []))

/-! ## Proof -/

def oddS (l : List α) : Slot α := (odd l).map (·, false)

theorem cnt_none : ∀ (l : List α) (s : List (Slot α)),
    cntS H l (none :: s) = oddS l :: cntS H (pairs H l) s ∧
    cntP H l (none :: s) = cntP H (pairs H l) s
  | [], _ => by simp [cntS, cntP, oddS, odd, pairs]
  | [_], _ => by simp [cntS, cntP, insS, insP, oddS, odd, pairs]
  | a :: b :: t, s => by
    have ih := cnt_none t (insS H (H a b) false s)
    simp [cntS, cntP, insS, insP, push, oddS, odd, pairs, ih.1, ih.2]

theorem cntS_append : ∀ (p : List α) (h : α) (s : List (Slot α)),
    cntS H (p ++ [h]) s = insS H h false (cntS H p s)
  | [], _, _ => rfl
  | _ :: p, h, s => by simp [cntS, cntS_append p h]

theorem cntP_append : ∀ (p : List α) (h : α) (s : List (Slot α)),
    cntP H (p ++ [h]) s = cntP H p s ++ insP H h false (cntS H p s)
  | [], _, _ => by simp [cntP, cntS]
  | _ :: p, h, s => by simp [cntP, cntS, cntP_append p h]

theorem insS_any (h : α) (m : Bool) : ∀ s : List (Slot α),
    (insS H h m s).any Option.isSome = true
  | [] => by simp [insS]
  | none :: _ => by simp [insS]
  | some (x, mx) :: s => by simp [insS, insS_any (H x h) (m || mx) s]

theorem cntS_any : ∀ (l : List α) (s : List (Slot α)),
    s.any Option.isSome = true → (cntS H l s).any Option.isSome = true
  | [], _, h => h
  | a :: t, s, _ => cntS_any t _ (insS_any H a false s)

theorem not_all_none_of_any_some' : ∀ c : List (Slot α),
    c.any Option.isSome = true → c.all Option.isNone = false
  | [], h => by simp at h
  | some _ :: _, _ => by simp
  | none :: c, h => by
    have := not_all_none_of_any_some' c (by simpa using h)
    simpa using this

theorem carryB_eq : ∀ (s : List (Slot α)) (h : α) (m : Bool),
    carryB H h m s = insP H h m s ++ finishB H (insS H h m s)
  | [], h, m => by simp [carryB, insP, insS, finishB, topB]
  | some (x, mx) :: s, h, m => by
    simp [carryB, insP, insS, finishB, carryB_eq s (H x h) (m || mx)]
  | none :: s, h, m => by simp [carryB, insP, insS, finishB, topB]

/-- **The constant-space branch of position 0 is the tree's branch.** -/
theorem branchCS0_eq_branch0 (l : List α) : branchCS0 H l = branch0 H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [branchCS0, branch0]
    | [a], _ => simp [branchCS0, branch0, cntP, cntS, insS, finishB, topB]
    | a :: b :: t, hn =>
      have hc := cnt_none H t [some (H a b, true)]
      have hlen := length_pairs H t
      rw [branch0, level]
      simp only [branchCS0, cntS, cntP, insS, insP, push, Bool.or_true, Bool.false_eq_true,
        ite_false, ite_true, hc.1, hc.2, List.nil_append, List.cons_append, List.cons.injEq,
        true_and]
      rw [level_eq]
      cases ho : odd t with
      | none =>
        simp only [oddS, ho, Option.map_none, finishB, List.append_nil]
        have := ih _ (by subst hn; simp only [List.length_cons, hlen]; omega)
          (H a b :: pairs H t) rfl
        simpa [branchCS0, insS] using this
      | some z =>
        have hne : (cntS H (pairs H t) [some (H a b, true)]).all Option.isNone = false :=
          not_all_none_of_any_some' _ (cntS_any H _ _ (by simp))
        have hodd := length_odd t
        rw [ho] at hodd
        have hodd' : t.length % 2 = 1 := by simpa using hodd.symm
        have := ih _ (by
            subst hn
            simp only [List.length_cons, List.length_append, hlen, List.length_nil]
            omega)
          (H a b :: (pairs H t ++ [H z z])) rfl
        simp only [oddS, ho, Option.map_some, finishB, topB, hne, Bool.false_eq_true, ite_false,
          List.nil_append, carryB_eq]
        simpa [branchCS0, insS, cntS_append, cntP_append, List.append_assoc] using this

/-- **End to end, for the light client.** Folding any replacement first leaf
`x` through the branch that the constant-space computation emits for position
0 of `y :: t` gives the root that the constant-space computation returns for
`x :: t`. -/
theorem fold_branchCS0 (x y : α) (t : List α) :
    some (fold H x ((branchCS0 H (y :: t)).map some) 0) = rootCS H (x :: t) := by
  rw [branchCS0_eq_branch0, ← branch_zero, fold_branch_zero, rootCS_eq_root]

end Bsv.Merkle
