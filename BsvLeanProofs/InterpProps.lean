import BsvLeanProofs.Interp

/-!
# First properties of the interpreter model

* Decoding an instruction always consumes at least one byte, so the loop's
  fuel (`script.length + 1`) is never exhausted: `run` gives the same answer
  for every sufficient fuel (`run_fuel`). This removes the one place where the
  definition could silently accept (its `fuel = 0` case).
* `CastToBool` is false on zero strings and on negative zero of any length.
-/

namespace Bsv.Interp

open Bsv.ScriptNum Bsv.Splice

theorem getOp_length {s : List Byte} {o : Nat} {d : Elem} {rest : List Byte}
    (h : getOp s = some (o, d, rest)) : rest.length < s.length := by
  cases s with
  | nil => simp [getOp] at h
  | cons b t =>
    simp only [getOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, h3⟩ := h
      subst h3
      simp
    · have hk : ∃ k, rest = t.drop k := by
        repeat' split at h
        all_goals first
          | (cases h; done)
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h
             exact ⟨_, by rw [← h.2.2, List.drop_drop]⟩)
      obtain ⟨k, rfl⟩ := hk
      simp only [List.length_drop, List.length_cons]
      omega

/-- The verdict does not depend on the fuel once it exceeds the script length. -/
theorem run_fuel_eq (c : Cfg) : ∀ (f1 f2 : Nat) (script : List Byte) (s : State),
    script.length < f1 → script.length < f2 → run c f1 script s = run c f2 script s
  | 0, _, _, _, h1, _ => by omega
  | _ + 1, 0, _, _, _, h2 => by omega
  | f1 + 1, f2 + 1, script, s, h1, h2 => by
    simp only [run]
    split
    · rfl
    · split
      · rfl
      · rename_i o d rest hg
        have hl := getOp_length hg
        split
        · rfl
        · rfl
        · exact run_fuel_eq c f1 f2 rest _ (by omega) (by omega)

theorem run_fuel (c : Cfg) (fuel : Nat) (script : List Byte) (s : State)
    (h : script.length < fuel) : run c fuel script s = run c (script.length + 1) script s :=
  run_fuel_eq c fuel (script.length + 1) script s h (by omega)

theorem castToBool_zeros : ∀ n : Nat, castToBool (List.replicate n 0#8) = false
  | 0 => rfl
  | 1 => by decide
  | n + 2 => by
    have ih := castToBool_zeros (n + 1)
    simp only [List.replicate_succ] at ih ⊢
    simp [castToBool, ih]

/-- Negative zero of any length is false. -/
theorem castToBool_negZero : ∀ n : Nat, castToBool (List.replicate n 0#8 ++ [0x80#8]) = false
  | 0 => by decide
  | n + 1 => by
    have ih := castToBool_negZero n
    cases n with
    | zero => decide
    | succ m =>
      simp only [List.replicate_succ, List.cons_append] at ih ⊢
      simp [castToBool, ih]

end Bsv.Interp
