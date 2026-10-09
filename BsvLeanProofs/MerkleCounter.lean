import BsvLeanProofs.Merkle

/-!
# The constant-space Merkle computation computes the tree's root

`MerkleComputation` (bitcoin-sv `consensus/merkle.cpp`, also ported as
`fn compute` in an independent Rust node implementation) keeps one pending subtree hash
per level and a leaf count, and finishes with a sweep up the right-hand edge.

What is modelled: the root computation, with the pending hashes as a list of
slots, lowest level first: slot `k` is `some h` exactly when bit `k` of the
count is set, and `h` is then `inner[k]`. Adding a leaf is a binary increment
with carries (`insert`); the final sweep is `finish`.
What is assumed in this file: that this slot list is a correct reading of the
source's array `inner` and counter `count`. `MerkleLiteral` removes that
assumption for the root: it models the array and the counter directly and
proves the result equal to the one here.
What is not modelled: the mutation flag and the branch output.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-- Add one leaf (or a carried subtree hash) at the lowest level. -/
def insert (h : α) : List (Option α) → List (Option α)
  | [] => [some h]
  | none :: s => some h :: s
  | some x :: s => none :: insert (H x h) s

/-- The slots after all leaves of `l` have been added to `s`. -/
def counter (l : List α) (s : List (Option α)) : List (Option α) :=
  l.foldl (fun s h => insert H h s) s

/-- The inner loop of the sweep: `h` has just been combined with itself and is
carried up through occupied levels; at a free level it stops, and is combined
with itself again unless nothing is pending above. -/
def carry (h : α) : List (Option α) → α
  | [] => h
  | some x :: s => carry (H x h) s
  | none :: s => if s.all Option.isNone then h else carry (H h h) s

/-- The outer loop of the sweep, from a hash `h` at an occupied level. -/
def top (h : α) (s : List (Option α)) : α :=
  if s.all Option.isNone then h else carry H (H h h) s

/-- The sweep: start from the lowest occupied level. -/
def finish : List (Option α) → Option α
  | [] => none
  | none :: s => finish s
  | some h :: s => some (top H h s)

/-- The root as the constant-space computation produces it. -/
def rootCS (l : List α) : Option α := finish H (counter H l [])

/-! ## Proof -/

/-- The complete pairs of a level. -/
def pairs : List α → List α
  | a :: b :: t => H a b :: pairs t
  | _ => []

/-- The unpaired last node of a level, if its length is odd. -/
def odd : List α → Option α
  | [] => none
  | [a] => some a
  | _ :: _ :: t => odd t

theorem level_eq : ∀ l : List α,
    level H l = pairs H l ++ (match odd l with | none => [] | some z => [H z z])
  | [] => by simp [level, pairs, odd]
  | [_] => by simp [level, pairs, odd]
  | _ :: _ :: t => by simp [level, pairs, odd, level_eq t]

theorem length_pairs : ∀ l : List α, (pairs H l).length = l.length / 2
  | [] => by simp [pairs]
  | [_] => by simp [pairs]
  | _ :: _ :: t => by simp only [pairs, List.length_cons, length_pairs t]; omega

theorem length_odd : ∀ l : List α, (odd l).isSome = (l.length % 2 == 1)
  | [] => by simp [odd]
  | [_] => by simp [odd]
  | _ :: _ :: t => by simp only [odd, List.length_cons, length_odd t]; congr 1; omega

theorem counter_cons (a : α) (t : List α) (s : List (Option α)) :
    counter H (a :: t) s = counter H t (insert H a s) := rfl

theorem counter_append (p : List α) (h : α) (s : List (Option α)) :
    counter H (p ++ [h]) s = insert H h (counter H p s) := by
  simp [counter, List.foldl_append]

/-- Adding the leaves of a level to a counter whose lowest slot is free leaves
the unpaired node in that slot and adds the pairs one level up. -/
theorem counter_none : ∀ (l : List α) (s : List (Option α)),
    counter H l (none :: s) = odd l :: counter H (pairs H l) s
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, s => by
    simp only [counter_cons, insert, pairs, odd]
    exact counter_none t _

theorem counter_nil (a b : α) (t : List α) :
    counter H (a :: b :: t) [] = odd (a :: b :: t) :: counter H (pairs H (a :: b :: t)) [] := by
  simp only [counter_cons, insert, pairs, odd]
  exact counter_none H t _

theorem insert_any (h : α) : ∀ s : List (Option α), (insert H h s).any Option.isSome = true
  | [] => by simp [insert]
  | none :: _ => by simp [insert]
  | some x :: s => by simp [insert, insert_any (H x h) s]

theorem counter_any : ∀ (l : List α) (s : List (Option α)),
    s.any Option.isSome = true → (counter H l s).any Option.isSome = true
  | [], _, h => h
  | a :: t, s, _ => by
    rw [counter_cons]; exact counter_any t _ (insert_any H a s)

theorem not_all_none_of_any_some : ∀ c : List (Option α),
    c.any Option.isSome = true → c.all Option.isNone = false
  | [], h => by simp at h
  | some _ :: _, _ => by simp
  | none :: c, h => by
    have := not_all_none_of_any_some c (by simpa using h)
    simpa using this

theorem counter_not_all_none (a : α) (t : List α) :
    (counter H (a :: t) []).all Option.isNone = false :=
  not_all_none_of_any_some _ (counter_any H t _ (insert_any H a []))

/-- Carrying a hash up and sweeping is the same as adding it and sweeping. -/
theorem carry_eq : ∀ (s : List (Option α)) (h : α),
    some (carry H h s) = finish H (insert H h s)
  | [], h => by simp [carry, insert, finish, top]
  | some x :: s, h => by simp only [carry, insert, finish]; exact carry_eq s _
  | none :: s, h => by simp [carry, insert, finish, top]

/-- **The constant-space computation returns the root of the tree**, for every
list of leaves and every combining function. -/
theorem rootCS_eq_root (l : List α) : rootCS H l = root H l := by
  unfold rootCS
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [counter, finish, root]
    | [a], _ => simp [counter, insert, finish, top, root]
    | a :: b :: t, hn =>
      have hlen := length_pairs H (a :: b :: t)
      rw [counter_nil, root, level_eq]
      cases ho : odd (a :: b :: t) with
      | none =>
        simp only [finish, List.append_nil]
        exact ih _ (by subst hn; rw [hlen]; simp only [List.length_cons]; omega) _ rfl
      | some z =>
        have hne : (counter H (pairs H (a :: b :: t)) []).all Option.isNone = false := by
          simp only [pairs]; exact counter_not_all_none H _ _
        simp only [finish, top, hne, Bool.false_eq_true, ite_false]
        rw [carry_eq, ← counter_append]
        have hodd := length_odd (a :: b :: t)
        rw [ho] at hodd
        simp only [Option.isSome_some, List.length_cons] at hodd
        have hodd' : (t.length + 1 + 1) % 2 = 1 := by simpa using hodd.symm
        exact ih _ (by
          subst hn
          simp only [List.length_append, hlen, List.length_cons, List.length_nil]
          omega) _ rfl

end Bsv.Merkle
