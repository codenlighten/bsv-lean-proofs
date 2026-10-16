import BsvLeanProofs.InterpProps

/-!
# One-instruction lemmas for the interpreter model

`run` reads an instruction with `getOp`, executes it with `step`, and recurses.
This file states what ONE instruction does when it SUCCEEDS, so that a proof about
a whole script can be a chain of rewrites. Each lemma carries the checks `step`
makes (size, operation count, disabled opcodes, stack limits) as hypotheses; none
of them describes an error outcome.

* `getOp_op`, `getOp_push`: how an opcode byte, or a short push (0 to 75 bytes), is
  decoded; PUSHDATA1/2/4 decoding is not covered;
* `run_cont`, `run_nil`: how `run` consumes a decoded instruction. `run_cont`
  needs positive fuel, and `evalScript` supplies `script.length + 1`, so a
  whole-script proof should use `run_fuel` (InterpProps) first;
* `step_push`, `step_plain`, `step_if`, `step_else`, `step_endif`: what `step`
  does in an executing state (every enclosing conditional taken, no OP_RETURN);
  `step_if_skip`, `step_skip`: what it does while a branch is skipped;
  `step_return_done`, `step_return_cond`: OP_RETURN after Genesis;
* `execOp_*`: the stack effect of single opcodes.

Not covered here: OP_VERIF / OP_VERNOTIF (0x65, 0x66), PUSHDATA decoding, the error outcomes
of `step`, and OP_RETURN while skipping or before Genesis. They are in `InterpCases.lean`.

Everything is about the Lean text of `Interp.lean`; whether that text is
`EvalScript` is the subject of `difftest/README.md`.
-/

namespace Bsv.Interp

open Bsv.ScriptNum Bsv.Splice

/-- The state after an instruction passes `fin`'s checks. -/
def finOk (c : Cfg) (s : State) : Bool :=
  !(!c.p.afterGenesis && decide (s.stack.length + s.alt.length > 1000)) &&
  !(s.stack.any (fun e => decide (e.length > c.budget)))

/-- A state in which instructions execute: every enclosing conditional is taken and
OP_RETURN has not run. -/
def Executing (s : State) : Prop := s.conds.all (·.1) = true ∧ s.ret = false

theorem run_cont {c : Cfg} {f : Nat} {script rest : List Byte} {o : Nat} {d : Elem}
    {s s' : State} (hne : script.isEmpty = false) (hg : getOp script = some (o, d, rest))
    (hs : step c s o d = .cont s') : run c (f + 1) script s = run c f rest s' := by
  simp [run, hne, hg, hs]

theorem run_nil {c : Cfg} {f : Nat} {s : State} (h : s.conds = []) :
    run c (f + 1) [] s = .ok s := by
  simp [run, h]

/-- A short push: the opcode byte is the length, 0 to 75. -/
theorem getOp_push {b : Byte} {d rest : List Byte} (h : b.toNat < 0x4c)
    (hl : d.length = b.toNat) : getOp (b :: (d ++ rest)) = some (b.toNat, d, rest) := by
  have h1 : ¬ (0x4e < b.toNat) := by omega
  simp [getOp, h1, h, hl]

theorem getOp_op {b : Byte} {rest : List Byte} (h : 0x4e < b.toNat) :
    getOp (b :: rest) = some (b.toNat, [], rest) := by
  simp [getOp, h]

/-- The operation counter after executing opcode `o`. -/
def opsAfter (s : State) (o : Nat) : Nat := if o > 0x60 then s.ops + 1 else s.ops

/-- A push: in an executing state, the data goes on the stack. -/
theorem step_push {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : Executing s)
    (ho : o ≤ 0x4e) (hmo : s.ops ≤ c.maxOps) (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmin : c.p.requireMinimal = true → minimalPush d o = true)
    (hfin : finOk c { s with stack := d :: s.stack, ops := s.ops } = true) :
    step c s o d = .cont { s with stack := d :: s.stack } := by
  obtain ⟨h1, h2⟩ := hx
  have hops : opsAfter s o = s.ops := by simp [opsAfter]; omega
  simp only [finOk, Bool.and_eq_true, Bool.not_eq_true'] at hfin
  have h3 : ¬ (o > 0x60) := by omega
  have hmin' : c.p.requireMinimal = true → minimalPush d o = true := hmin
  rcases s with ⟨st, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo hfin ⊢
  subst h2
  obtain ⟨hf1, hf2⟩ := hfin
  simp at hf1 hf2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩; rcases hsz with h | h <;> simp_all <;> omega
  have n2 : ¬ (c.maxOps < ops) := by omega
  have n3 : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by omega
  have n4 : ¬ (c.p.requireMinimal = true ∧ minimalPush d o = false) := by
    rintro ⟨a, b⟩; simp_all
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < st.length + 1 + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (c.budget < d.length ∨ ∃ x, x ∈ st ∧ c.budget < x.length) := by
    rintro (h | ⟨x, hx, h⟩)
    · have := hf2.1; omega
    · have := hf2.2 x hx; omega
  simp [step, h1, h3, ho, n1, n2, n3, n4, n5, n6]

/-- Any other executed opcode: its effect is whatever `execOp` returns. -/
theorem step_plain {c : Cfg} {s : State} {o : Nat} {st alt : Stack} (hx : Executing s)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = false) (he : execOp c o s.stack s.alt = .ok (st, alt))
    (hfin : finOk c { s with stack := st, alt := alt, ops := opsAfter s o } = true) :
    step c s o [] = .cont { s with stack := st, alt := alt, ops := opsAfter s o } := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true', Bool.not_eq_true] at hf1 hf2
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob he hf1 hf2 hmo
  subst h2
  simp at hf1 hf2
  have o0 : ¬ (o ≤ 0x4e) := by omega
  have o1 : o ≠ 0x63 := by omega
  have o2 : o ≠ 0x64 := by omega
  have o3 : o ≠ 0x65 := by omega
  have o4 : o ≠ 0x66 := by omega
  have o5 : o ≠ 0x67 := by omega
  have o6 : o ≠ 0x68 := by omega
  have hd : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by
    rintro ⟨a, b⟩; have := hdis a; simp_all
  by_cases o7 : 96 < o
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops + 1 := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he]
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < st.length + alt.length) := by
      rintro ⟨a, b⟩; have := hf1 a; omega
    have n6 : ¬ (∃ x, x ∈ st ∧ c.budget < x.length) := by
      rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
    simp [n2, n5, n6]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he]
    have n2 : ¬ (c.maxOps < ops) := by omega
    have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < st.length + alt.length) := by
      rintro ⟨a, b⟩; have := hf1 a; omega
    have n6 : ¬ (∃ x, x ∈ st ∧ c.budget < x.length) := by
      rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
    simp [n2, n5, n6]

/-- OP_ELSE (any state: it also runs while a branch is being skipped). -/
theorem step_else {c : Cfg} {s : State} {b e : Bool} {r : List (Bool × Bool)}
    (hc : s.conds = (b, e) :: r) (hmo : s.ops + 1 ≤ c.maxOps)
    (hne : ¬(e = true ∧ c.p.afterGenesis = true))
    (hfin : finOk c { s with conds := (!b, true) :: r, ops := s.ops + 1 } = true) :
    step c s 0x67 [] = .cont { s with conds := (!b, true) :: r, ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo hf1 hf2 ⊢
  subst hc
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, n2, n5, n6]
  intro he
  cases hag : c.p.afterGenesis <;> simp_all

/-- OP_ENDIF (any state). -/
theorem step_endif {c : Cfg} {s : State} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hc : s.conds = x :: r) (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with conds := r, ops := s.ops + 1 } = true) :
    step c s 0x68 [] = .cont { s with conds := r, ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo hf1 hf2 ⊢
  subst hc
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, n2, n5, n6]

/-- OP_IF / OP_NOTIF in an executing state: pops the condition and opens a
conditional that is taken iff the condition's truth (negated for OP_NOTIF) holds. -/
theorem step_if {c : Cfg} {s : State} {o : Nat} {v : Elem} {r : Stack}
    (hx : Executing s) (ho : o = 0x63 ∨ o = 0x64) (hst : s.stack = v :: r)
    (hmo : s.ops + 1 ≤ c.maxOps)
    (hmi : ¬(c.minimalIf = true ∧ (v.length > 1 ∨ (v.length = 1 ∧ v ≠ [1#8]))))
    (hfin : finOk c { s with stack := r, conds := ((if o = 0x64 then !castToBool v else castToBool v), false) :: s.conds,
                             ops := s.ops + 1 } = true) :
    step c s o [] = .cont { s with stack := r, conds := ((if o = 0x64 then !castToBool v else castToBool v), false) :: s.conds,
                                   ops := s.ops + 1 } := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hst hmo hf1 hf2 ⊢
  subst h2 hst
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < r.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ r ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl
  · simp [step, h1, n2, n5, n6]
    intro hm
    have h3 := fun h => hmi ⟨hm, h⟩
    refine ⟨?_, fun hl => ?_⟩
    · exact Nat.le_of_not_lt (fun hh => h3 (Or.inl hh))
    · exact Classical.byContradiction (fun hh => h3 (Or.inr ⟨hl, hh⟩))
  · simp [step, h1, n2, n5, n6]
    intro hm
    have h3 := fun h => hmi ⟨hm, h⟩
    refine ⟨?_, fun hl => ?_⟩
    · exact Nat.le_of_not_lt (fun hh => h3 (Or.inl hh))
    · exact Classical.byContradiction (fun hh => h3 (Or.inr ⟨hl, hh⟩))

theorem fExec_false {s : State} {o : Nat} (hx : ¬Executing s) (ho : o ≠ 0x6a) :
    ((s.conds.all (·.1)) && (!s.ret || o == 0x6a)) = false := by
  simp only [Executing, not_and] at hx
  cases ha : s.conds.all (·.1)
  · rfl
  · have := hx ha
    have hr : s.ret = true := by cases h : s.ret <;> simp_all
    simp [hr, ho]

/-- OP_IF / OP_NOTIF / OP_VERIF / OP_VERNOTIF-free case: a conditional OPENED while
a branch is being skipped is itself skipped, and consumes nothing. -/
theorem step_if_skip {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x63 ∨ o = 0x64) (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } = true) :
    step c s o [] = .cont { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only [Executing] at hx hmo hf1 hf2 ⊢
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  have hx' : ¬ ((conds.all fun x => x.fst) = true ∧ ret = false) := hx
  have hfe := fExec_false (s := { stack := stk, alt := alt, conds := conds, ops := ops, ret := ret }) (o := o)
    (fun h => hx h) (by omega)
  simp only [] at hfe
  rcases ho with rfl | rfl <;> simp only [step] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx' ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [n2, n5, n6]

/-- If the size, operation-count, disabled-opcode and stack checks pass, an
instruction other than a conditional or OP_RETURN, met while a branch is being
skipped, changes only the operation counter. -/
theorem step_skip {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : ¬Executing s)
    (ho : o ≠ 0x6a) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68))
    (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmo : opsAfter s o ≤ c.maxOps)
    (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true ∨ c.p.afterGenesis = true)
    (hfin : finOk c { s with ops := opsAfter s o } = true) :
    step c s o d = .cont { s with ops := opsAfter s o } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  have hfe := fExec_false (s := s) (o := o) hx ho
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only [] at hfe hmo hf1 hf2
  simp at hf1 hf2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩; rcases hsz with h | h <;> simp_all <;> omega
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have o1 : o ≠ 0x63 := by omega
  have o2 : o ≠ 0x64 := by omega
  have o3 : o ≠ 0x65 := by omega
  have o4 : o ≠ 0x66 := by omega
  have o5 : o ≠ 0x67 := by omega
  have o6 : o ≠ 0x68 := by omega
  have o8 : ¬ (99 ≤ o) ∨ ¬ (o ≤ 104) := by omega
  have hd : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false ∧ c.p.afterGenesis = false) := by
    rintro ⟨a, b, e⟩; rcases hdis a with h | h <;> simp_all
  have hd' : ¬ (((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) ∧ c.p.afterGenesis = false) := by
    rintro ⟨⟨a, b⟩, e⟩; exact hd ⟨a, b, e⟩
  by_cases o7 : 96 < o
  · have e7 : opsAfter { stack := stk, alt := alt, conds := conds, ops := ops, ret := ret } o = ops + 1 := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp only [step]
    generalize (conds.all fun x => x.fst) = A at hfe ⊢
    cases A <;> cases ret <;> first | (simp at hfe; done) | simp [o1, o2, o3, o4, o5, o6, o7, o8, hnc, ho, n1, n2, n5, n6, hd, hd']
  · have e7 : opsAfter { stack := stk, alt := alt, conds := conds, ops := ops, ret := ret } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp only [step]
    generalize (conds.all fun x => x.fst) = A at hfe ⊢
    cases A <;> cases ret <;> first | (simp at hfe; done) | simp [o1, o2, o3, o4, o5, o6, o7, o8, hnc, ho, n1, n2, n5, n6, hd, hd']

/-! ### Stack effect of single opcodes (`execOp`) -/

section ExecOp
variable (c : Cfg) (alt : Stack)

theorem execOp_small (o : Nat) (h1 : 0x51 ≤ o) (h2 : o ≤ 0x60) (st : Stack) :
    execOp c o st alt = .ok (encInt (Int.ofNat (o - 0x50)) :: st, alt) := by
  have h3 : o ≠ 0x4f := by omega
  simp [execOp, h3, h1, h2]

theorem execOp_1negate (st : Stack) : execOp c 0x4f st alt = .ok (encInt (-1) :: st, alt) := by
  simp [execOp]

theorem execOp_toalt (x : Elem) (r : Stack) :
    execOp c 0x6b (x :: r) alt = .ok (r, x :: alt) := by simp [execOp]

theorem execOp_toalt_nil : execOp c 0x6b [] alt = .error (.op .invalidStackOperation) := by
  simp [execOp]

theorem execOp_fromalt (x : Elem) (r st : Stack) :
    execOp c 0x6c st (x :: r) = .ok (x :: st, r) := by simp [execOp]

theorem execOp_fromalt_nil (st : Stack) :
    execOp c 0x6c st [] = .error .invalidAltstackOperation := by simp [execOp]

theorem execOp_drop (x : Elem) (r : Stack) : execOp c 0x75 (x :: r) alt = .ok (r, alt) := by
  simp [execOp]

theorem execOp_dup (x : Elem) (r : Stack) : execOp c 0x76 (x :: r) alt = .ok (x :: x :: r, alt) := by
  simp [execOp]

theorem execOp_nip (a x : Elem) (r : Stack) : execOp c 0x77 (a :: x :: r) alt = .ok (a :: r, alt) := by
  simp [execOp]

theorem execOp_over (a b : Elem) (r : Stack) :
    execOp c 0x78 (a :: b :: r) alt = .ok (b :: a :: b :: r, alt) := by
  simp [execOp]

theorem execOp_rot (x3 x2 x1 : Elem) (r : Stack) :
    execOp c 0x7b (x3 :: x2 :: x1 :: r) alt = .ok (x1 :: x3 :: x2 :: r, alt) := by
  simp [execOp]

theorem execOp_swap (a b : Elem) (r : Stack) :
    execOp c 0x7c (a :: b :: r) alt = .ok (b :: a :: r, alt) := by
  simp [execOp]

theorem execOp_verify (x : Elem) (r : Stack) (h : castToBool x = true) :
    execOp c 0x69 (x :: r) alt = .ok (r, alt) := by
  simp [execOp, h]

theorem execOp_equal (b a : Elem) (r : Stack) :
    execOp c 0x87 (b :: a :: r) alt = .ok ((if a == b then [1#8] else []) :: r, alt) := by
  simp [execOp]

theorem execOp_pick (n x : Elem) (r : Stack) (v : Int) (hn : num c.p n = .ok v)
    (h0 : 0 ≤ v) (h1 : v < ((x :: r).length : Int)) :
    execOp c 0x79 (n :: x :: r) alt = .ok ((x :: r).getD v.toNat [] :: (x :: r), alt) := by
  simp [execOp, hn, not_or, h0, h1]
  simpa using h1

theorem execOp_roll (n x : Elem) (r : Stack) (v : Int) (hn : num c.p n = .ok v)
    (h0 : 0 ≤ v) (h1 : v < ((x :: r).length : Int)) :
    execOp c 0x7a (n :: x :: r) alt =
      .ok ((x :: r).getD v.toNat [] :: (x :: r).eraseIdx v.toNat, alt) := by
  simp [execOp, hn, not_or, h0, h1]
  simpa using h1

theorem execOp_pick_range (n x : Elem) (r : Stack) (v : Int) (hn : num c.p n = .ok v)
    (h : v < 0 ∨ v ≥ ((x :: r).length : Int)) :
    execOp c 0x79 (n :: x :: r) alt = .error (.op .invalidStackOperation) := by
  simp [execOp, hn]
  intro h0
  simp at h
  omega

theorem execOp_cat (st : Stack) :
    execOp c 0x7e st alt = (liftE (opCat c.p st)).map (·, alt) := by simp [execOp, modelled]

theorem execOp_split (st : Stack) :
    execOp c 0x7f st alt = (liftE (opSplit c.p st)).map (·, alt) := by simp [execOp, modelled]

theorem execOp_num2bin (st : Stack) :
    execOp c 0x80 st alt = (liftE (opNum2Bin c.p st)).map (·, alt) := by simp [execOp, modelled]

theorem execOp_bin2num (st : Stack) :
    execOp c 0x81 st alt = (liftE (opBin2Num c.p st)).map (·, alt) := by simp [execOp, modelled]

theorem execOp_not (x : Elem) (r : Stack) (v : Int) (hn : num c.p x = .ok v) :
    execOp c 0x91 (x :: r) alt = .ok (encInt (boolInt (v == 0)) :: r, alt) := by
  simp [execOp, modelled, unaryOf, opUnary, hn, liftE, Except.map]

theorem execOp_boolAnd (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) :
    execOp c 0x9a (x2 :: x1 :: r) alt = .ok (encInt (boolInt (a != 0 && b != 0)) :: r, alt) := by
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, liftE, Except.map]

theorem execOp_boolOr (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) :
    execOp c 0x9b (x2 :: x1 :: r) alt = .ok (encInt (boolInt (a != 0 || b != 0)) :: r, alt) := by
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, liftE, Except.map]

theorem execOp_numEqual (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) :
    execOp c 0x9c (x2 :: x1 :: r) alt = .ok (encInt (boolInt (a == b)) :: r, alt) := by
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, liftE, Except.map]

theorem execOp_numNotEqual (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) :
    execOp c 0x9e (x2 :: x1 :: r) alt = .ok (encInt (boolInt (a != b)) :: r, alt) := by
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, liftE, Except.map]

end ExecOp

/-- OP_RETURN after Genesis, outside any conditional: the script ends successfully. -/
theorem step_return_done {c : Cfg} {s : State} (hx : Executing s)
    (hag : c.p.afterGenesis = true) (hc : s.conds = []) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x6a [] = .done { s with ops := s.ops + 1 } := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc h2 hmo
  subst hc h2
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, hag, n2]

/-- OP_RETURN after Genesis, inside a conditional: execution continues with the
`ret` flag set, so later instructions are skipped (except the conditional ones). -/
theorem step_return_cond {c : Cfg} {s : State} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hx : Executing s) (hag : c.p.afterGenesis = true) (hc : s.conds = x :: r)
    (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with ret := true, ops := s.ops + 1 } = true) :
    step c s 0x6a [] = .cont { s with ret := true, ops := s.ops + 1 } := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc h2 hmo h1 hf1 hf2
  subst hc h2
  simp at hf1 hf2
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  have n6 : ¬ (∃ y, y ∈ stk ∧ c.budget < y.length) := by
    rintro ⟨y, hy, h⟩; have := hf2 y hy; omega
  simp [step, hag, n2, n6, h1]

/-- After Genesis, a minimally encoded number reads back as itself (the reader
used for PICK, SPLIT and NUM2BIN indices and for the arithmetic operands). -/
theorem num_encInt {p : Params} (n : Int) (hag : p.afterGenesis = true)
    (hl : (encInt n).length ≤ p.maxNumLen) : num p (encInt n) = .ok n := by
  have hm := isMinimal_encInt n
  by_cases he : (encInt n).isEmpty = true
  · have h0 : encInt n = [] := List.isEmpty_iff.mp he
    have hd : denote ([] : Elem) = 0 := by decide
    have hn : n = 0 := by
      have := denote_encInt n
      rw [h0, hd] at this
      exact this.symm
    subst hn
    rw [h0] at hm hl
    simp [num, scriptNum, h0, isMinimalMax, hm, hl]
  · simp [num, scriptNum, hag, hm, isMinimalMax, hl, he, denote_encInt]

/-! ### The lemmas compose

A one-opcode script, run from an arbitrary executing state: the chain
`getOp_op`, `step_plain`, `execOp_swap`, `run_nil` is the whole proof, and longer
scripts repeat it. -/

theorem run_swap {c : Cfg} {f : Nat} {s : State} {a b : Elem} {r : Stack}
    (hx : Executing s) (hst : s.stack = a :: b :: r) (hmo : s.ops + 1 ≤ c.maxOps)
    (hnil : s.conds = [])
    (hfin : finOk c { s with stack := b :: a :: r, ops := s.ops + 1 } = true) :
    run c (f + 1 + 1) [0x7c#8] s = .ok { s with stack := b :: a :: r, ops := s.ops + 1 } := by
  have hg : getOp [0x7c#8] = some (0x7c, [], []) := getOp_op (by decide)
  have hob : overBudget c 0x7c s.stack = false := by simp [overBudget]
  have hstep := step_plain (c := c) (s := s) (o := 0x7c) (st := b :: a :: r) (alt := s.alt) hx
    (by decide) (by decide) (by decide) (by simpa [opsAfter] using hmo)
    (by intro h; omega) hob (by rw [hst]; exact execOp_swap c s.alt a b r)
    (by simpa [opsAfter] using hfin)
  rw [run_cont (by rfl) hg hstep]
  simpa [opsAfter] using run_nil (c := c) (f := f) (s := { s with stack := b :: a :: r, alt := s.alt, ops := opsAfter s 0x7c }) hnil

end Bsv.Interp
