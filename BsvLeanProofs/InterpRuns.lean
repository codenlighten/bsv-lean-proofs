import BsvLeanProofs.InterpSteps

/-!
# Straight-line scripts as rewriting chains

`runs c script s` is `run` with the fuel `evalScript` supplies (`script.length + 1`). A fragment
lemma has the shape

  `runs c (frag ++ rest) (Sx s0 stk n) = runs c rest (Sx s0 stk' n')`

for every continuation `rest`, so a longer fragment is a chain of rewrites finished by `runs_nil`.
The lemmas are the success cases of `InterpSteps.lean` lifted to whole scripts.

* `Good c`: after Genesis, `maxNumLen >= 1`, `budget >= 75`.
* `Base s0`: the base state is outside every conditional and has not returned.
* `Sx s0 stk n`: `s0` with main stack `stk` and operation counter `n`; `alt` is untouched.
* `Sc s0 stk n cs`: the same inside the open conditionals `cs`.
* `Fits c stk`: every element is at most `c.budget` bytes (the `finOk` side condition).

These definitions and lemmas were developed for the compiler-correctness proof of a Boolean
gate fragment (a separate project that imports this library) and moved here because nothing in
them mentions gates.
-/

open Bsv.Interp Bsv.Splice Bsv.ScriptNum

namespace Bsv.Interp
structure Good (c : Cfg) : Prop where
  ag : c.p.afterGenesis = true
  mnl : 1 ≤ c.p.maxNumLen
  bud : 75 ≤ c.budget

def Base (s0 : State) : Prop := s0.conds = [] ∧ s0.ret = false

def Sx (s0 : State) (stk : Stack) (n : Nat) : State := { s0 with stack := stk, ops := n }

def Fits (c : Cfg) (stk : Stack) : Prop := ∀ e ∈ stk, e.length ≤ c.budget

/-- `run` with the fuel `evalScript` supplies. -/
def runs (c : Cfg) (script : List Byte) (s : State) : Except IErr State :=
  run c (script.length + 1) script s

@[simp] theorem Fits_nil (c : Cfg) : Fits c [] := by intro e he; simp at he
@[simp] theorem Fits_cons (c : Cfg) (x : Elem) (r : Stack) :
    Fits c (x :: r) ↔ x.length ≤ c.budget ∧ Fits c r := by
  constructor
  · intro h; exact ⟨h x (by simp), fun e he => h e (by simp [he])⟩
  · rintro ⟨h1, h2⟩ e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h1
    · exact h2 e he
theorem Fits_append (c : Cfg) (a b : Stack) : Fits c (a ++ b) ↔ Fits c a ∧ Fits c b := by
  constructor
  · intro h; exact ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩
  · rintro ⟨h1, h2⟩ e he
    rcases List.mem_append.mp he with he | he
    · exact h1 e he
    · exact h2 e he
theorem Fits.mem {c : Cfg} {stk : Stack} (h : Fits c stk) {e : Elem} (he : e ∈ stk) : e.length ≤ c.budget := h e he
theorem Fits.of_sub {c : Cfg} {stk stk' : Stack} (h : Fits c stk) (hs : ∀ e ∈ stk', e ∈ stk) : Fits c stk' :=
  fun e he => h e (hs e he)

theorem Sx_executing {s0 : State} (hb : Base s0) (stk : Stack) (n : Nat) : Executing (Sx s0 stk n) := by
  obtain ⟨h1, h2⟩ := hb
  simp [Executing, Sx, h1, h2]

theorem finOk_Sx {c : Cfg} (hG : Good c) {s0 : State} {stk : Stack} {n : Nat} (hf : Fits c stk) :
    finOk c (Sx s0 stk n) = true := by
  have h1 : c.p.afterGenesis = true := hG.ag
  simp only [finOk, Sx, h1, Bool.not_true, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
  intro e he
  exact Nat.not_lt.mpr (hf e he)

/-- `run` with any sufficient fuel is `runs`. -/
theorem run_eq_runs (c : Cfg) {fuel : Nat} {script : List Byte} {s : State} (h : script.length < fuel) :
    run c fuel script s = runs c script s := run_fuel c fuel script s h

/-- The end of a straight-line script. -/
theorem runs_nil {c : Cfg} {s0 : State} (hb : Base s0) (stk : Stack) (n : Nat) :
    runs c [] (Sx s0 stk n) = .ok (Sx s0 stk n) := by
  have : (Sx s0 stk n).conds = [] := hb.1
  simpa [runs] using run_nil (c := c) (f := 0) this

theorem runs_cons {c : Cfg} {b : Byte} {tail rest : List Byte} {o : Nat} {d : Elem} {s s' : State}
    (hg : getOp (b :: tail) = some (o, d, rest)) (hs : step c s o d = .cont s') :
    runs c (b :: tail) s = runs c rest s' := by
  have hl := getOp_length hg
  have h1 : run c ((tail.length + 1) + 1) (b :: tail) s = run c (tail.length + 1) rest s' :=
    run_cont (by rfl) hg hs
  have h2 : run c (tail.length + 1) rest s' = run c (rest.length + 1) rest s' :=
    run_fuel_eq c _ _ rest s' (by simp at hl; omega) (by omega)
  simp only [runs, List.length_cons]
  rw [h1, h2]

/-- Any executed non-conditional opcode (`0x4e < o`) whose `execOp` leaves `alt` alone.
`o` is the opcode as a number; `hbo` ties it to the byte. -/
theorem runs_exec {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {b : Byte} {o : Nat}
    {rest : List Byte} {stk stk' : Stack} {n n' : Nat} (hbo : b.toNat = o)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hdis : o ≠ 0x8d ∧ o ≠ 0x8e)
    (hn' : (if 0x60 < o then n + 1 else n) = n') (hmo : n' ≤ c.maxOps)
    (hob : overBudget c o stk = false)
    (he : execOp c o stk s0.alt = .ok (stk', s0.alt)) (hf : Fits c stk') :
    runs c (b :: rest) (Sx s0 stk n) = runs c rest (Sx s0 stk' n') := by
  subst hbo
  have hg : getOp (b :: rest) = some (b.toNat, [], rest) := getOp_op ho
  have hops : opsAfter (Sx s0 stk n) b.toNat = n' := by
    simp only [opsAfter, Sx]; exact hn'
  have hs := step_plain (c := c) (s := Sx s0 stk n) (o := b.toNat) (st := stk') (alt := s0.alt)
    (Sx_executing hb stk n) ho hnc h6a (by rw [hops]; exact hmo)
    (fun h => by
      rcases h with h | h
      · exact absurd h hdis.1
      · exact absurd h hdis.2) hob
    (by simpa [Sx] using he)
    (by rw [hops]; exact finOk_Sx hG hf)
  rw [runs_cons hg (s' := Sx s0 stk' n') (by rw [hs, hops]; rfl)]

/-- A direct push (opcode byte = length, 0 to 75 bytes), minimal. -/
theorem runs_push {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {b : Byte} {d rest : List Byte}
    {stk : Stack} {n : Nat}
    (hlt : b.toNat < 0x4c) (hd : d.length = b.toNat) (hmin : minimalPush d b.toNat = true)
    (hmo : n ≤ c.maxOps) (hf : Fits c (d :: stk)) :
    runs c (b :: (d ++ rest)) (Sx s0 stk n) = runs c rest (Sx s0 (d :: stk) n) := by
  have hg : getOp (b :: (d ++ rest)) = some (b.toNat, d, rest) := getOp_push hlt hd
  have hs := step_push (c := c) (s := Sx s0 stk n) (o := b.toNat) (d := d) (Sx_executing hb stk n)
    (by omega) hmo (Or.inl hG.ag) (fun _ => hmin) (finOk_Sx hG hf)
  rw [runs_cons hg hs]
  rfl

def Sc (s0 : State) (stk : Stack) (n : Nat) (cs : List (Bool × Bool)) : State :=
  { s0 with stack := stk, ops := n, conds := cs }

theorem Sc_nil {s0 : State} (hb : Base s0) (stk : Stack) (n : Nat) : Sc s0 stk n [] = Sx s0 stk n := by
  obtain ⟨h1, h2⟩ := hb
  simp [Sc, Sx, h1]

theorem finOk_Sc {c : Cfg} (hG : Good c) {s0 : State} {stk : Stack} {n : Nat} {cs : List (Bool × Bool)}
    (hf : Fits c stk) : finOk c (Sc s0 stk n cs) = true := by
  have := finOk_Sx hG (s0 := s0) (stk := stk) (n := n) hf
  simpa [finOk, Sc, Sx] using this

theorem Sc_executing {s0 : State} (hret : s0.ret = false) {cs : List (Bool × Bool)}
    (hcs : cs.all (·.1) = true) (stk : Stack) (n : Nat) : Executing (Sc s0 stk n cs) := by
  simp [Executing, Sc, hret, hcs]

theorem Sc_not_executing {s0 : State} {cs : List (Bool × Bool)} (hcs : cs.all (·.1) = false)
    (stk : Stack) (n : Nat) : ¬ Executing (Sc s0 stk n cs) := by
  simp [Executing, Sc, hcs]

/-- `runs_exec` inside an executing conditional. -/
theorem runs_exec_c {c : Cfg} (hG : Good c) {s0 : State} (hret : s0.ret = false)
    {cs : List (Bool × Bool)} (hcs : cs.all (·.1) = true) {b : Byte} {o : Nat}
    {rest : List Byte} {stk stk' : Stack} {n n' : Nat} (hbo : b.toNat = o)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hdis : o ≠ 0x8d ∧ o ≠ 0x8e)
    (hn' : (if 0x60 < o then n + 1 else n) = n') (hmo : n' ≤ c.maxOps)
    (hob : overBudget c o stk = false)
    (he : execOp c o stk s0.alt = .ok (stk', s0.alt)) (hf : Fits c stk') :
    runs c (b :: rest) (Sc s0 stk n cs) = runs c rest (Sc s0 stk' n' cs) := by
  subst hbo
  have hg : getOp (b :: rest) = some (b.toNat, [], rest) := getOp_op ho
  have hops : opsAfter (Sc s0 stk n cs) b.toNat = n' := by
    simp only [opsAfter, Sc]; exact hn'
  have hs := step_plain (c := c) (s := Sc s0 stk n cs) (o := b.toNat) (st := stk') (alt := s0.alt)
    (Sc_executing hret hcs stk n) ho hnc h6a (by rw [hops]; exact hmo)
    (fun h => by
      rcases h with h | h
      · exact absurd h hdis.1
      · exact absurd h hdis.2) hob
    (by simpa [Sc] using he)
    (by rw [hops]; exact finOk_Sc hG hf)
  rw [runs_cons hg (s' := Sc s0 stk' n' cs) (by rw [hs, hops]; rfl)]

/-- A counted opcode met while a branch is skipped changes only the operation counter. -/
theorem runs_skip_c {c : Cfg} (hG : Good c) {s0 : State}
    {cs : List (Bool × Bool)} (hcs : cs.all (·.1) = false) {b : Byte} {o : Nat}
    {rest : List Byte} {stk : Stack} {n : Nat} (hbo : b.toNat = o)
    (ho : 0x60 < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hdis : o = 0x8d ∨ o = 0x8e → c.p.chronicleOps = true ∨ c.p.afterGenesis = true)
    (hmo : n + 1 ≤ c.maxOps) (hf : Fits c stk) :
    runs c (b :: rest) (Sc s0 stk n cs) = runs c rest (Sc s0 stk (n + 1) cs) := by
  subst hbo
  have hg : getOp (b :: rest) = some (b.toNat, [], rest) := getOp_op (by omega)
  have hops : opsAfter (Sc s0 stk n cs) b.toNat = n + 1 := by
    simp [opsAfter, Sc, ho]
  have hs := step_skip (c := c) (s := Sc s0 stk n cs) (o := b.toNat) (d := [])
    (Sc_not_executing hcs stk n) h6a hnc (Or.inl hG.ag) (by rw [hops]; exact hmo) hdis
    (by rw [hops]; exact finOk_Sc hG hf)
  rw [runs_cons hg (s' := Sc s0 stk (n + 1) cs) (by rw [hs, hops]; rfl)]

/-- OP_IF on `v` in an executing (top-level) state. -/
theorem runs_if {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {rest : List Byte} {n : Nat}
    {v : Elem} {r : Stack}
    (hmi : ¬(c.minimalIf = true ∧ (v.length > 1 ∨ (v.length = 1 ∧ v ≠ [1#8]))))
    (hmo : n + 1 ≤ c.maxOps) (hf : Fits c r) :
    runs c (0x63#8 :: rest) (Sx s0 (v :: r) n)
      = runs c rest (Sc s0 r (n + 1) [(castToBool v, false)]) := by
  have hg : getOp (0x63#8 :: rest) = some (0x63, [], rest) := getOp_op (by decide)
  have hs := step_if (c := c) (s := Sx s0 (v :: r) n) (o := 0x63) (v := v) (r := r)
    (Sx_executing hb _ _) (Or.inl rfl) rfl hmo hmi
    (by
      have := finOk_Sc hG (s0 := s0) (stk := r) (n := n + 1) (cs := (castToBool v, false) :: s0.conds) hf
      simpa [Sx, Sc] using this)
  rw [runs_cons hg (s' := Sc s0 r (n + 1) [(castToBool v, false)])
    (by rw [hs]; simp [Sx, Sc, hb.1])]

theorem runs_else {c : Cfg} (hG : Good c) {s0 : State} {rest : List Byte} {n : Nat}
    {stk : Stack} {bb e : Bool} {r : List (Bool × Bool)}
    (hne : ¬(e = true ∧ c.p.afterGenesis = true)) (hmo : n + 1 ≤ c.maxOps) (hf : Fits c stk) :
    runs c (0x67#8 :: rest) (Sc s0 stk n ((bb, e) :: r))
      = runs c rest (Sc s0 stk (n + 1) ((!bb, true) :: r)) := by
  have hg : getOp (0x67#8 :: rest) = some (0x67, [], rest) := getOp_op (by decide)
  have hs := step_else (c := c) (s := Sc s0 stk n ((bb, e) :: r)) (b := bb) (e := e) (r := r) rfl
    hmo hne (finOk_Sc hG hf)
  rw [runs_cons hg (s' := Sc s0 stk (n + 1) ((!bb, true) :: r)) (by rw [hs]; rfl)]

theorem runs_endif {c : Cfg} (hG : Good c) {s0 : State} {rest : List Byte} {n : Nat}
    {stk : Stack} {x : Bool × Bool} {r : List (Bool × Bool)}
    (hmo : n + 1 ≤ c.maxOps) (hf : Fits c stk) :
    runs c (0x68#8 :: rest) (Sc s0 stk n (x :: r)) = runs c rest (Sc s0 stk (n + 1) r) := by
  have hg : getOp (0x68#8 :: rest) = some (0x68, [], rest) := getOp_op (by decide)
  have hs := step_endif (c := c) (s := Sc s0 stk n (x :: r)) (x := x) (r := r) rfl
    hmo (finOk_Sc hG hf)
  rw [runs_cons hg (s' := Sc s0 stk (n + 1) r) (by rw [hs]; rfl)]

end Bsv.Interp
