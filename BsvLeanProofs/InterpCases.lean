import BsvLeanProofs.InterpRuns

/-!
# The remaining cases of `getOp`, `step` and `run`

`InterpSteps.lean` covers the successful cases of one instruction. This file adds the rest.
It is a lemma for each branch of `getOp`, `step` and `run`, not a single theorem that the
hypotheses of the lemmas leave no case out; the map below is how the branches are covered.

* `getOp`: PUSHDATA1/2/4 decoding (`getOp_pushdata1/2/4`) and the truncated forms that make it
  fail (`getOp_none_*`); the empty script is `rfl`.
* `run`: one lemma for each outcome of one step (`run_getOp_none`, `run_err`, `run_done`,
  `run_nil_unbalanced`, `run_zero`; `run_cont` and `run_nil` are in `InterpSteps.lean`).
* `step`, in the order `EvalScript` applies its checks:
  - before any opcode: `step_err_pushSize`, `step_err_opCount`, `step_err_disabled`;
  - executed push: `step_err_minimalData`, and `step_push_fin`;
  - executed other opcode: `step_plain_err` (the opcode fails), `step_plain_outOfModel`
    (the model declines a large operand) and `step_plain_fin`;
  - every branch that ends in the local `fin` (stack-count limit before Genesis, then the
    element budget) is stated once as `step = finOut c s'`: `step_push_fin`, `step_plain_fin`,
    `step_else_fin`, `step_endif_fin`, `step_if_fin`, `step_if_skip_fin`, `step_verif_fin`,
    `step_verif_skip_fin`, `step_verif_skip_nochron_fin`, `step_skip_fin`,
    `step_return_skip_fin`, `step_return_cond_fin`. `finOut_ok`, `finOut_stackSize` and
    `finOut_budget` turn that into the success case or either failure;
  - conditionals: `step_if_err_empty`, `step_if_err_minimalIf`, `step_else_err_empty`,
    `step_else_err_twice`, `step_endif_err_empty`;
  - OP_VERIF and OP_VERNOTIF, both eras, executed and skipped (`step_verif_*`);
  - OP_RETURN: `step_return_err_pre` (before Genesis), `step_return_skip`,
    `step_return_done_any`, `step_return_cond_any`.
* Whole scripts: `runs_return` (after Genesis, OP_RETURN outside a conditional ends the run
  without decoding what follows) and `runs_getOp_none`. Neither says anything about
  `evalScript` or `verify`, which add size, flag and final-stack checks.

The `Sanity` section at the end runs the model by kernel evaluation and discharges every
hypothesis of a lemma on a concrete state, so no lemma is vacuous.

Everything is about the Lean text of `Interp.lean`, as in `InterpSteps.lean`.
-/

namespace Bsv.Interp

open Bsv.ScriptNum Bsv.Splice

/-! ### `getOp`: PUSHDATA -/

theorem getOp_nil : getOp [] = none := rfl

theorem getOp_pushdata1 {n : Byte} {d rest : List Byte} (hl : d.length = n.toNat) :
    getOp (0x4c#8 :: n :: (d ++ rest)) = some (0x4c, d, rest) := by
  simp [getOp, leNat, hl]

theorem getOp_pushdata2 {lo hi : Byte} {d rest : List Byte}
    (hl : d.length = lo.toNat + 256 * hi.toNat) :
    getOp (0x4d#8 :: lo :: hi :: (d ++ rest)) = some (0x4d, d, rest) := by
  simp [getOp, leNat, hl]

theorem getOp_pushdata4 {b0 b1 b2 b3 : Byte} {d rest : List Byte}
    (hl : d.length = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) :
    getOp (0x4e#8 :: b0 :: b1 :: b2 :: b3 :: (d ++ rest)) = some (0x4e, d, rest) := by
  simp [getOp, leNat, hl]

/-- A direct push whose data is cut short. -/
theorem getOp_none_direct {b : Byte} {rest : List Byte} (h : b.toNat < 0x4c)
    (hl : rest.length < b.toNat) : getOp (b :: rest) = none := by
  have h1 : ¬ (0x4e < b.toNat) := by omega
  simp [getOp, h1, h, hl]

/-- The length field of a PUSHDATA is cut short. -/
theorem getOp_none_pushdata1_hdr : getOp [0x4c#8] = none := by simp [getOp]
theorem getOp_none_pushdata2_hdr (x : List Byte) (hx : x.length < 2) :
    getOp (0x4d#8 :: x) = none := by simp [getOp, hx]
theorem getOp_none_pushdata4_hdr (x : List Byte) (hx : x.length < 4) :
    getOp (0x4e#8 :: x) = none := by simp [getOp, hx]

/-- PUSHDATA1 whose data is shorter than its length byte says. -/
theorem getOp_none_pushdata1_body {n : Byte} {x : List Byte} (hl : x.length < n.toNat) :
    getOp (0x4c#8 :: n :: x) = none := by
  simp [getOp, leNat, hl]

theorem getOp_none_pushdata2_body {lo hi : Byte} {x : List Byte}
    (hl : x.length < lo.toNat + 256 * hi.toNat) : getOp (0x4d#8 :: lo :: hi :: x) = none := by
  simp [getOp, leNat, hl]

theorem getOp_none_pushdata4_body {b0 b1 b2 b3 : Byte} {x : List Byte}
    (hl : x.length < b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) :
    getOp (0x4e#8 :: b0 :: b1 :: b2 :: b3 :: x) = none := by
  simp [getOp, leNat, hl]

/-! ### `run`: each outcome -/

theorem run_zero (c : Cfg) (script : List Byte) (s : State) : run c 0 script s = .ok s := rfl

theorem run_getOp_none {c : Cfg} {f : Nat} {script : List Byte} {s : State}
    (hne : script.isEmpty = false) (hg : getOp script = none) :
    run c (f + 1) script s = .error .badOpcode := by
  simp [run, hne, hg]

theorem run_err {c : Cfg} {f : Nat} {script rest : List Byte} {o : Nat} {d : Elem} {s : State}
    {e : IErr} (hne : script.isEmpty = false) (hg : getOp script = some (o, d, rest))
    (hs : step c s o d = .err e) : run c (f + 1) script s = .error e := by
  simp [run, hne, hg, hs]

theorem run_done {c : Cfg} {f : Nat} {script rest : List Byte} {o : Nat} {d : Elem}
    {s s' : State} (hne : script.isEmpty = false) (hg : getOp script = some (o, d, rest))
    (hs : step c s o d = .done s') : run c (f + 1) script s = .ok s' := by
  simp [run, hne, hg, hs]

/-- The end of the script with a conditional still open. -/
theorem run_nil_unbalanced {c : Cfg} {f : Nat} {s : State} (h : s.conds ≠ []) :
    run c (f + 1) [] s = .error .unbalancedConditional := by
  have : s.conds.isEmpty = false := by
    cases hc : s.conds
    · exact absurd hc h
    · rfl
  simp [run, this]

/-! ### `step`: the checks that fail before any opcode runs -/

theorem step_err_pushSize {c : Cfg} {s : State} {o : Nat} {d : Elem}
    (hag : c.p.afterGenesis = false) (hd : 520 < d.length) :
    step c s o d = .err (.op .pushSize) := by
  simp [step, hag, hd]

theorem step_err_opCount {c : Cfg} {s : State} {o : Nat} {d : Elem}
    (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520) (h : c.maxOps < opsAfter s o) :
    step c s o d = .err .opCount := by
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  by_cases o7 : o > 0x60
  · simp [opsAfter, o7] at h
    simp [step, n1, o7, h]
  · simp [opsAfter, o7] at h
    simp [step, n1, o7, h]

/-- OP_2MUL and OP_2DIV are disabled unless Chronicle is active; before Genesis the check
applies even while a branch is skipped. -/
theorem step_err_disabled {c : Cfg} {s : State} {o : Nat} {d : Elem}
    (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520) (hmo : opsAfter s o ≤ c.maxOps)
    (ho : o = 0x8d ∨ o = 0x8e) (hc : c.p.chronicleOps = false)
    (hcond : c.p.afterGenesis = false ∨ Executing s) :
    step c s o d = .err (.op .disabledOpcode) := by
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  have o7 : o > 0x60 := by omega
  have n2 : ¬ (c.maxOps < s.ops + 1) := by simp [opsAfter, o7] at hmo; omega
  have h6a : o ≠ 0x6a := by omega
  rcases hcond with hag | ⟨h1, h2⟩
  · have hl : d.length ≤ 520 := by
      rcases hsz with h | h
      · rw [hag] at h; exact absurd h (by decide)
      · exact h
    rcases ho with rfl | rfl <;> simp [step, n2, hc, hag, hl]
  · rcases ho with rfl | rfl <;> simp [step, n1, n2, hc, h1, h2]

/-! ### `step`: errors of pushes and plain opcodes -/

theorem step_err_minimalData {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : Executing s)
    (ho : o ≤ 0x4e) (hmo : s.ops ≤ c.maxOps) (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hreq : c.p.requireMinimal = true) (hmin : minimalPush d o = false) :
    step c s o d = .err .minimalData := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : ¬ (o > 0x60) := by omega
  rcases s with ⟨st, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo
  subst h2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  have n2 : ¬ (c.maxOps < ops) := by omega
  have n3 : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by omega
  simp [step, h1, h3, ho, n1, n2, n3, hreq, hmin]

/-- A push that would take main plus alt stack past 1000 items before Genesis. -/
theorem step_push_err_stackSize {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : Executing s)
    (ho : o ≤ 0x4e) (hmo : s.ops ≤ c.maxOps) (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmin : c.p.requireMinimal = true → minimalPush d o = true)
    (hag : c.p.afterGenesis = false) (hbig : 1000 < s.stack.length + 1 + s.alt.length) :
    step c s o d = .err .stackSize := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : ¬ (o > 0x60) := by omega
  rcases s with ⟨st, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo hbig
  subst h2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  have n2 : ¬ (c.maxOps < ops) := by omega
  have n3 : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by omega
  have n4 : ¬ (c.p.requireMinimal = true ∧ minimalPush d o = false) := by
    rintro ⟨a, b⟩; have := hmin a; simp_all
  have hl : d.length ≤ 520 := by
    rcases hsz with h | h
    · rw [hag] at h; exact absurd h (by decide)
    · exact h
  simp [step, h1, h3, ho, hl, n2, n3, n4, hag, hbig]

/-- A push that leaves an element above the modelled size budget (and does not hit the
stack-count limit first). -/
theorem step_push_err_budget {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : Executing s)
    (ho : o ≤ 0x4e) (hmo : s.ops ≤ c.maxOps) (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmin : c.p.requireMinimal = true → minimalPush d o = true)
    (hcnt : ¬(c.p.afterGenesis = false ∧ 1000 < s.stack.length + 1 + s.alt.length))
    (hbig : c.budget < d.length ∨ ∃ x, x ∈ s.stack ∧ c.budget < x.length) :
    step c s o d = .err .outOfModel := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : ¬ (o > 0x60) := by omega
  rcases s with ⟨st, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo hbig hcnt
  subst h2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  have n2 : ¬ (c.maxOps < ops) := by omega
  have n3 : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by omega
  have n4 : ¬ (c.p.requireMinimal = true ∧ minimalPush d o = false) := by
    rintro ⟨a, b⟩; have := hmin a; simp_all
  simp [step, h1, h3, ho, n1, n2, n3, n4, hcnt, hbig]

/-- Any other executed opcode whose `execOp` fails: that error is the outcome. -/
theorem step_plain_err {c : Cfg} {s : State} {o : Nat} {e : IErr} (hx : Executing s)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = false) (he : execOp c o s.stack s.alt = .error e) :
    step c s o [] = .err e := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob he hmo
  subst h2
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
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2]

/-- The model declines to evaluate an opcode whose operand (or the result it would have to
build) is above the budget (`overBudget`); such scripts are set aside, not judged. -/
theorem step_plain_outOfModel {c : Cfg} {s : State} {o : Nat} (hx : Executing s)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = true) :
    step c s o [] = .err .outOfModel := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob hmo
  subst h2
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
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, n2]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, n2]

/-- A plain opcode whose result would take main plus alt stack past 1000 items before Genesis. -/
theorem step_plain_err_stackSize {c : Cfg} {s : State} {o : Nat} {st alt : Stack}
    (hx : Executing s) (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = false) (he : execOp c o s.stack s.alt = .ok (st, alt))
    (hag : c.p.afterGenesis = false) (hbig : 1000 < st.length + alt.length) :
    step c s o [] = .err .stackSize := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob he hmo
  subst h2
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
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2, hag, hbig]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2, hag, hbig]

/-- A plain opcode whose result has an element above the budget (and which does not hit the
stack-count limit first). -/
theorem step_plain_err_budget {c : Cfg} {s : State} {o : Nat} {st alt : Stack}
    (hx : Executing s) (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = false) (he : execOp c o s.stack s.alt = .ok (st, alt))
    (hcnt : ¬(c.p.afterGenesis = false ∧ 1000 < st.length + alt.length))
    (hbig : ∃ x, x ∈ st ∧ c.budget < x.length) :
    step c s o [] = .err .outOfModel := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob he hmo
  subst h2
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
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2, hcnt, hbig]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp [step, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2, hcnt, hbig]

/-! ### `step`: conditionals -/

/-- OP_IF / OP_NOTIF with an empty stack. -/
theorem step_if_err_empty {c : Cfg} {s : State} {o : Nat} (hx : Executing s)
    (ho : o = 0x63 ∨ o = 0x64) (hst : s.stack = []) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = .err .unbalancedConditional := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hst hmo
  subst h2 hst
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp [step, h1, n2]

/-- OP_IF / OP_NOTIF with MINIMALIF set and a condition that is not exactly empty or 1. -/
theorem step_if_err_minimalIf {c : Cfg} {s : State} {o : Nat} {v : Elem} {r : Stack}
    (hx : Executing s) (ho : o = 0x63 ∨ o = 0x64) (hst : s.stack = v :: r)
    (hmo : s.ops + 1 ≤ c.maxOps)
    (hmi : c.minimalIf = true ∧ (v.length > 1 ∨ (v.length = 1 ∧ v ≠ [1#8]))) :
    step c s o [] = .err .minimalIf := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hm, hv⟩ := hmi
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hst hmo
  subst h2 hst
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  have hv' : (decide (v.length > 1) || (v.length == 1 && v != [1#8])) = true := by
    rcases hv with h | ⟨h, h'⟩
    · simp [h]
    · simp [h, h']
  rcases ho with rfl | rfl <;> simp [step, h1, n2, hm, hv']

/-- OP_ELSE with no open conditional (it runs in every state). -/
theorem step_else_err_empty {c : Cfg} {s : State} (hc : s.conds = [])
    (hmo : s.ops + 1 ≤ c.maxOps) : step c s 0x67 [] = .err .unbalancedConditional := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, n2]

/-- A second OP_ELSE in the same conditional, after Genesis. -/
theorem step_else_err_twice {c : Cfg} {s : State} {b : Bool} {r : List (Bool × Bool)}
    (hc : s.conds = (b, true) :: r) (hag : c.p.afterGenesis = true)
    (hmo : s.ops + 1 ≤ c.maxOps) : step c s 0x67 [] = .err .unbalancedConditional := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, n2, hag]

/-- OP_ENDIF with no open conditional. -/
theorem step_endif_err_empty {c : Cfg} {s : State} (hc : s.conds = [])
    (hmo : s.ops + 1 ≤ c.maxOps) : step c s 0x68 [] = .err .unbalancedConditional := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, n2]

/-! ### OP_VERIF and OP_VERNOTIF (0x65, 0x66) -/

/-- Before Chronicle, executed: an invalid opcode. -/
theorem step_verif_err_exec {c : Cfg} {s : State} {o : Nat} (hx : Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = false)
    (hmo : s.ops + 1 ≤ c.maxOps) : step c s o [] = .err .badOpcode := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo
  subst h2
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp [step, h1, hc, n2]

/-- Before Chronicle, met while a branch is skipped, before Genesis: still an invalid opcode. -/
theorem step_verif_err_skip_pre {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = false)
    (hag : c.p.afterGenesis = false) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = .err .badOpcode := by
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp [step, hc, hag, n2, hfe]

/-- Before Chronicle, met while a branch is skipped, after Genesis: ignored (but counted). -/
theorem step_verif_skip_nochron {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = false)
    (hag : c.p.afterGenesis = true) (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with ops := s.ops + 1 } = true) :
    step c s o [] = .cont { s with ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo hf1 hf2
  simp at hf1 hf2
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp only [step] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [hc, hag, n2, n6]

/-- With Chronicle active, executed, on an empty stack. -/
theorem step_verif_err_empty {c : Cfg} {s : State} {o : Nat} (hx : Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = true) (hst : s.stack = [])
    (hmo : s.ops + 1 ≤ c.maxOps) : step c s o [] = .err .unbalancedConditional := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo hst
  subst h2 hst
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp [step, h1, hc, n2]

/-- Whether the conditional opened by OP_VERIF (0x65) or OP_VERNOTIF (0x66) on `v` is taken. -/
def verifFlag (c : Cfg) (o : Nat) (v : Elem) : Bool :=
  if o = 0x66 then !(v == le4 c.txVersion) else v == le4 c.txVersion

/-- With Chronicle active, executed: the top of the stack is compared with the four-byte
little-endian transaction version; OP_VERNOTIF negates the comparison. -/
theorem step_verif {c : Cfg} {s : State} {o : Nat} {v : Elem} {r : Stack} (hx : Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = true) (hst : s.stack = v :: r)
    (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with stack := r, conds := (verifFlag c o v, false) :: s.conds, ops := s.ops + 1 } = true) :
    step c s o [] = .cont { s with stack := r, conds := (verifFlag c o v, false) :: s.conds, ops := s.ops + 1 } := by
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
  rcases ho with rfl | rfl <;> simp [step, verifFlag, h1, hc, n2, n5, n6]

/-- With Chronicle active, met while a branch is skipped: opens a conditional that is not
taken, consuming nothing. -/
theorem step_verif_skip {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = true) (hmo : s.ops + 1 ≤ c.maxOps)
    (hfin : finOk c { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } = true) :
    step c s o [] = .cont { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo hf1 hf2
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp only [step] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [hc, n2, n5, n6]

/-! ### OP_RETURN -/

/-- Before Genesis, with every enclosing conditional taken (whether or not `ret` is set): an
error. -/
theorem step_return_err_pre {c : Cfg} {s : State} (hact : s.conds.all (·.1) = true)
    (hag : c.p.afterGenesis = false) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x6a [] = .err .opReturn := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hact hmo
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, hact, hag, n2]

/-- While a branch is skipped (some enclosing conditional is not taken), OP_RETURN is
ignored and only counted. -/
theorem step_return_skip {c : Cfg} {s : State} (hact : s.conds.all (·.1) = false)
    (hmo : s.ops + 1 ≤ c.maxOps) (hfin : finOk c { s with ops := s.ops + 1 } = true) :
    step c s 0x6a [] = .cont { s with ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hact hmo hf1 hf2
  simp at hf1 hf2
  have n5 : ¬ (c.p.afterGenesis = false ∧ 1000 < stk.length + alt.length) := by
    rintro ⟨a, b⟩; have := hf1 a; omega
  have n6 : ¬ (∃ x, x ∈ stk ∧ c.budget < x.length) := by
    rintro ⟨x, hx, h⟩; have := hf2 x hx; omega
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, hact, n2, n5, n6]

/-- OP_RETURN after Genesis outside any conditional, whether or not `ret` is already set. -/
theorem step_return_done_any {c : Cfg} {s : State} (hag : c.p.afterGenesis = true)
    (hc : s.conds = []) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x6a [] = .done { s with ops := s.ops + 1 } := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, hag, n2]

/-- OP_RETURN after Genesis inside a taken conditional, whether or not `ret` is already set. -/
theorem step_return_cond_any {c : Cfg} {s : State} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hag : c.p.afterGenesis = true) (hact : s.conds.all (·.1) = true) (hc : s.conds = x :: r)
    (hmo : s.ops + 1 ≤ c.maxOps) (hfin : finOk c { s with ret := true, ops := s.ops + 1 } = true) :
    step c s 0x6a [] = .cont { s with ret := true, ops := s.ops + 1 } := by
  obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.mp hfin
  simp only [Bool.not_eq_true'] at hf1 hf2
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hact hmo hf1 hf2
  subst hc
  simp at hf1 hf2
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  have n6 : ¬ (∃ y, y ∈ stk ∧ c.budget < y.length) := by
    rintro ⟨y, hy, h⟩; have := hf2 y hy; omega
  simp [step, hag, n2, n6, hact]

/-! ### Whole-script consequences -/

/-- After Genesis, OP_RETURN outside any conditional makes `runs` stop without decoding what
follows it (even bytes that would not decode). This is a statement about `runs`, not about
acceptance by `evalScript` or `verify`. -/
theorem runs_return {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {rest : List Byte}
    {stk : Stack} {n : Nat} (hmo : n + 1 ≤ c.maxOps) :
    runs c (0x6a#8 :: rest) (Sx s0 stk n) = .ok (Sx s0 stk (n + 1)) := by
  have hg : getOp (0x6a#8 :: rest) = some (0x6a, [], rest) := getOp_op (by decide)
  have hs := step_return_done (c := c) (s := Sx s0 stk n) (Sx_executing hb stk n) hG.ag hb.1 hmo
  exact run_done (f := rest.length + 1) (by rfl) hg hs

/-- A script whose next instruction cannot be decoded fails with `badOpcode`. -/
theorem runs_getOp_none {c : Cfg} {script : List Byte} {s : State} (hne : script ≠ [])
    (hg : getOp script = none) : runs c script s = .error .badOpcode := by
  have : script.isEmpty = false := by
    cases script
    · exact absurd rfl hne
    · rfl
  exact run_getOp_none this hg

/-! ### The final checks (`fin`) after every kind of instruction

`step` ends most branches with a local function `fin` that checks the stack-count limit before
Genesis and the element budget. `finOut` is that function; each lemma below says that a branch
of `step` ENDS in `finOut` of the state the successful lemma names, so the success case and
both failures (`stackSize`, then `outOfModel`) come from one statement. -/

/-- The local `fin` of `step`. -/
def finOut (c : Cfg) (s : State) : Out :=
  if !c.p.afterGenesis && decide (s.stack.length + s.alt.length > 1000) then .err .stackSize
  else if s.stack.any (fun e => decide (e.length > c.budget)) then .err .outOfModel
  else .cont s

theorem finOut_ok {c : Cfg} {s : State} (h : finOk c s = true) : finOut c s = .cont s := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  simp only [Bool.not_eq_true'] at h1 h2
  simp [finOut, h1, h2]

theorem finOut_stackSize {c : Cfg} {s : State} (hag : c.p.afterGenesis = false)
    (hbig : 1000 < s.stack.length + s.alt.length) : finOut c s = .err .stackSize := by
  simp [finOut, hag, hbig]

theorem finOut_budget {c : Cfg} {s : State}
    (hcnt : ¬(c.p.afterGenesis = false ∧ 1000 < s.stack.length + s.alt.length))
    (hbig : ∃ x, x ∈ s.stack ∧ c.budget < x.length) : finOut c s = .err .outOfModel := by
  obtain ⟨x, hx, h⟩ := hbig
  have : (s.stack.any (fun e => decide (e.length > c.budget))) = true :=
    List.any_eq_true.mpr ⟨x, hx, by simpa using h⟩
  have h1 : ¬ (c.p.afterGenesis = false ∧ 1000 < s.stack.length + s.alt.length) := hcnt
  simp [finOut, this, h1]

/-- A plain opcode: `step` ends in `finOut` of the state `execOp` gives. -/
theorem step_plain_fin {c : Cfg} {s : State} {o : Nat} {st alt : Stack} (hx : Executing s)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hmo : opsAfter s o ≤ c.maxOps) (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true)
    (hob : overBudget c o s.stack = false) (he : execOp c o s.stack s.alt = .ok (st, alt)) :
    step c s o [] = finOut c { s with stack := st, alt := alt, ops := opsAfter s o } := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt0, conds, ops, ret⟩
  simp only at h1 h2 hob he hmo
  subst h2
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
    have n2 : ¬ (c.maxOps < ops + 1) := by omega
    simp [step, finOut, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2]
  · have e7 : opsAfter { stack := stk, alt := alt0, conds := conds, ops := ops } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp [step, finOut, h1, o0, o1, o2, o3, o4, o5, o6, o7, h6a, hd, hob, he, n2]

/-- OP_ELSE (any state), when the pair is not a second OP_ELSE after Genesis. -/
theorem step_else_fin {c : Cfg} {s : State} {b e : Bool} {r : List (Bool × Bool)}
    (hc : s.conds = (b, e) :: r) (hmo : s.ops + 1 ≤ c.maxOps)
    (hne : ¬(e = true ∧ c.p.afterGenesis = true)) :
    step c s 0x67 [] = finOut c { s with conds := (!b, true) :: r, ops := s.ops + 1 } := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo ⊢
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, finOut, n2]
  intro he
  cases hag : c.p.afterGenesis <;> simp_all

/-- OP_ENDIF (any state). -/
theorem step_endif_fin {c : Cfg} {s : State} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hc : s.conds = x :: r) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x68 [] = finOut c { s with conds := r, ops := s.ops + 1 } := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hmo ⊢
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, finOut, n2]

/-- An instruction other than a conditional or OP_RETURN, met while a branch is skipped. -/
theorem step_skip_fin {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : ¬Executing s)
    (ho : o ≠ 0x6a) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68))
    (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmo : opsAfter s o ≤ c.maxOps)
    (hdis : (o = 0x8d ∨ o = 0x8e) → c.p.chronicleOps = true ∨ c.p.afterGenesis = true) :
    step c s o d = finOut c { s with ops := opsAfter s o } := by
  have hfe := fExec_false (s := s) (o := o) hx ho
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only [] at hfe hmo
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
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
    simp only [step, finOut]
    generalize (conds.all fun x => x.fst) = A at hfe ⊢
    cases A <;> cases ret <;> first | (simp at hfe; done) | simp [o1, o2, o3, o4, o5, o6, o7, o8, hnc, ho, n1, n2, hd, hd']
  · have e7 : opsAfter { stack := stk, alt := alt, conds := conds, ops := ops, ret := ret } o = ops := by
      simp [opsAfter, o7]
    rw [e7] at hmo ⊢
    have n2 : ¬ (c.maxOps < ops) := by omega
    simp only [step, finOut]
    generalize (conds.all fun x => x.fst) = A at hfe ⊢
    cases A <;> cases ret <;> first | (simp at hfe; done) | simp [o1, o2, o3, o4, o5, o6, o7, o8, hnc, ho, n1, n2, hd, hd']

/-- OP_RETURN while a branch is skipped. -/
theorem step_return_skip_fin {c : Cfg} {s : State} (hact : s.conds.all (·.1) = false)
    (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x6a [] = finOut c { s with ops := s.ops + 1 } := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hact hmo ⊢
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, finOut, hact, n2]

/-- OP_RETURN after Genesis inside a taken conditional. -/
theorem step_return_cond_fin {c : Cfg} {s : State} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hag : c.p.afterGenesis = true) (hact : s.conds.all (·.1) = true) (hc : s.conds = x :: r)
    (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s 0x6a [] = finOut c { s with ret := true, ops := s.ops + 1 } := by
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hc hact hmo ⊢
  subst hc
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  simp [step, finOut, hag, n2, hact]

/-- OP_IF / OP_NOTIF in an executing state, when the condition passes the MINIMALIF check. -/
theorem step_if_fin {c : Cfg} {s : State} {o : Nat} {v : Elem} {r : Stack}
    (hx : Executing s) (ho : o = 0x63 ∨ o = 0x64) (hst : s.stack = v :: r)
    (hmo : s.ops + 1 ≤ c.maxOps)
    (hmi : ¬(c.minimalIf = true ∧ (v.length > 1 ∨ (v.length = 1 ∧ v ≠ [1#8])))) :
    step c s o [] = finOut c { s with stack := r, conds := ((if o = 0x64 then !castToBool v else castToBool v), false) :: s.conds, ops := s.ops + 1 } := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hst hmo ⊢
  subst h2 hst
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl
  · simp [step, finOut, h1, n2]
    intro hm hv
    exact absurd ⟨hm, hv⟩ hmi
  · simp [step, finOut, h1, n2]
    intro hm hv
    exact absurd ⟨hm, hv⟩ hmi

/-- OP_IF / OP_NOTIF opened while a branch is skipped. -/
theorem step_if_skip_fin {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x63 ∨ o = 0x64) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = finOut c { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } := by
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo ⊢
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp only [step, finOut] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [n2]

/-- OP_VERIF / OP_VERNOTIF with Chronicle, met while a branch is skipped. -/
theorem step_verif_skip_fin {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = true) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = finOut c { s with conds := (false, false) :: s.conds, ops := s.ops + 1 } := by
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo ⊢
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp only [step, finOut] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [hc, n2]

/-- OP_VERIF / OP_VERNOTIF with Chronicle, executed, on a non-empty stack. -/
theorem step_verif_fin {c : Cfg} {s : State} {o : Nat} {v : Elem} {r : Stack} (hx : Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = true) (hst : s.stack = v :: r)
    (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = finOut c { s with stack := r, conds := (verifFlag c o v, false) :: s.conds, ops := s.ops + 1 } := by
  obtain ⟨h1, h2⟩ := hx
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at h1 h2 hst hmo ⊢
  subst h2 hst
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp [step, finOut, verifFlag, h1, hc, n2]

/-- OP_VERIF / OP_VERNOTIF without Chronicle, after Genesis, met while a branch is skipped. -/
theorem step_verif_skip_nochron_fin {c : Cfg} {s : State} {o : Nat} (hx : ¬Executing s)
    (ho : o = 0x65 ∨ o = 0x66) (hc : c.p.chronicleOps = false)
    (hag : c.p.afterGenesis = true) (hmo : s.ops + 1 ≤ c.maxOps) :
    step c s o [] = finOut c { s with ops := s.ops + 1 } := by
  have hfe := fExec_false (s := s) (o := o) hx (by omega)
  rcases s with ⟨stk, alt, conds, ops, ret⟩
  simp only at hfe hmo ⊢
  have n2 : ¬ (c.maxOps < ops + 1) := by omega
  rcases ho with rfl | rfl <;> simp only [step, finOut] <;>
  generalize (conds.all fun x => x.fst) = A at hfe hx ⊢ <;>
  cases A <;> cases ret <;> first | (simp at hfe; done) | simp [hc, hag, n2]

/-- A push: `step` ends in `finOut` of the state with the data on top. -/
theorem step_push_fin {c : Cfg} {s : State} {o : Nat} {d : Elem} (hx : Executing s)
    (ho : o ≤ 0x4e) (hmo : s.ops ≤ c.maxOps) (hsz : c.p.afterGenesis = true ∨ d.length ≤ 520)
    (hmin : c.p.requireMinimal = true → minimalPush d o = true) :
    step c s o d = finOut c { s with stack := d :: s.stack } := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : ¬ (o > 0x60) := by omega
  rcases s with ⟨st, alt, conds, ops, ret⟩
  simp only at h1 h2 hmo ⊢
  subst h2
  have n1 : ¬ (c.p.afterGenesis = false ∧ 520 < d.length) := by
    rintro ⟨a, b⟩
    rcases hsz with h | h
    · rw [a] at h; exact absurd h (by decide)
    · omega
  have n2 : ¬ (c.maxOps < ops) := by omega
  have n3 : ¬ ((o = 141 ∨ o = 142) ∧ c.p.chronicleOps = false) := by omega
  have n4 : ¬ (c.p.requireMinimal = true ∧ minimalPush d o = false) := by
    rintro ⟨a, b⟩; have := hmin a; simp_all
  simp [step, finOut, h1, h3, ho, n1, n2, n3, n4]

/-! ### Sanity instances

The lemmas above have many hypotheses. These instances run the model itself (kernel
evaluation, no lemma used) and, where a lemma applies, discharge every hypothesis of the lemma
on a concrete state, so that none is vacuous. `cBefore` is before Genesis, `cGenesis` after
Genesis, `cChron` after Chronicle (flag bits 19 and 21, `cfgOf`). -/

section Sanity

def cBefore : Cfg := cfgOf 1 1402863
def cGenesis : Cfg := cfgOf 1 (1402863 ||| (1 <<< 19))
def cChron : Cfg := cfgOf 1 (1402863 ||| (1 <<< 19) ||| (1 <<< 21))

example : getOp [0x4c#8, 3#8, 1#8, 2#8, 3#8, 9#8] = some (0x4c, [1#8, 2#8, 3#8], [9#8]) := by decide
example : getOp [0x4d#8, 1#8, 1#8] = none := by decide
example : getOp [0x4e#8, 1#8, 0#8, 0#8, 0#8] = none := by decide

-- pushdata lemmas on the same bytes
example : getOp (0x4c#8 :: 3#8 :: ([1#8, 2#8, 3#8] ++ [9#8])) = some (0x4c, [1#8, 2#8, 3#8], [9#8]) :=
  getOp_pushdata1 (by decide)
example : getOp (0x4d#8 :: 2#8 :: 0#8 :: ([1#8, 2#8] ++ [9#8])) = some (0x4d, [1#8, 2#8], [9#8]) :=
  getOp_pushdata2 (by decide)

-- OP_VERIF before Chronicle is an invalid opcode, executed
example : step cGenesis { stack := [[1#8]] } 0x65 [] = .err .badOpcode :=
  step_verif_err_exec ⟨rfl, rfl⟩ (Or.inl rfl) rfl (by decide)

-- OP_VERIF with Chronicle: the version 1 in little-endian is [1, 0, 0, 0]
example : step cChron { stack := [[1#8, 0#8, 0#8, 0#8]] } 0x65 [] =
    .cont { stack := [], conds := [(true, false)], ops := 1 } :=
  step_verif (v := [1#8, 0#8, 0#8, 0#8]) (r := []) ⟨rfl, rfl⟩ (Or.inl rfl) rfl rfl (by decide)
    (by decide)

example : step cChron { stack := [[1#8, 0#8, 0#8, 0#8]] } 0x66 [] =
    .cont { stack := [], conds := [(false, false)], ops := 1 } :=
  step_verif (v := [1#8, 0#8, 0#8, 0#8]) (r := []) ⟨rfl, rfl⟩ (Or.inr rfl) rfl rfl (by decide)
    (by decide)

-- OP_RETURN before Genesis is an error; after Genesis it ends the script
example : step cBefore {} 0x6a [] = .err .opReturn := step_return_err_pre rfl rfl (by decide)
example : step cGenesis {} 0x6a [] = .done { ops := 1 } :=
  step_return_done_any rfl rfl (by decide)

-- OP_RETURN while skipping is only counted
example : step cGenesis { conds := [(false, false)] } 0x6a [] =
    .cont { conds := [(false, false)], ops := 1 } :=
  step_return_skip rfl (by decide) (by decide)

-- an operation count past the limit
example : step cBefore { ops := 500 } 0x61 [] = .err .opCount :=
  step_err_opCount (Or.inr (by decide)) (by decide)

-- an oversized push before Genesis
example (d : Elem) (h : d.length = 521) : step cBefore {} 0x4d d = .err (.op .pushSize) :=
  step_err_pushSize rfl (by omega)

-- OP_ELSE and OP_ENDIF with nothing open
example : step cGenesis {} 0x67 [] = .err .unbalancedConditional := step_else_err_empty rfl (by decide)
example : step cGenesis {} 0x68 [] = .err .unbalancedConditional := step_endif_err_empty rfl (by decide)

-- the end of the script with a conditional open
example : run cGenesis 2 [] { conds := [(true, false)] } = .error .unbalancedConditional :=
  run_nil_unbalanced (by simp)

end Sanity

end Bsv.Interp
