import BsvLeanProofs.InterpRuns

/-!
# A 2-of-3 threshold counter on the alt stack

The script (32 bytes, no hash or signature opcode):

```
0 OP_TOALTSTACK
<"c3c3"> OP_EQUAL OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
<"c2c2"> OP_EQUAL OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
<"c1c1"> OP_EQUAL OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
OP_FROMALTSTACK OP_2 OP_GREATERTHANOREQUAL
```

hex `006b0463336333876c936b0463326332876c936b0463316331876c936b6c52a2`. With the three
"slots" `s1, s2, s3` on the stack (`s3` on top) it compares each slot with its own constant,
keeps the running count on the alt stack between slots, and leaves the truth value of
"count >= 2".

Results, about the model `Bsv.Interp` (after Genesis). Hypotheses: `Good c` (after Genesis,
`maxNumLen >= 1`, `budget >= 75`), every slot fits the element budget (`Fits`), the operation
limit allows 15 counted operations, and for `evalScript` also valid flags and `maxScriptSize >= 32`.

* `counter_runs`: from any executing top-level state with `[s3, s2, s1] ++ r` on the stack,
  the script ends with `encInt (boolInt (count >= 2)) :: r` on the stack, the alt stack
  EMPTY, and the operation counter 15 higher. The rest of the stack is untouched. `count` is
  the number of slots equal to their own constant (`s3` is compared with `c3` first).
* `counter_evalScript`: the same through `evalScript` with the slots as the starting stack.
  Under the hypotheses above no error arises, whatever the slots contain: the script always
  ends normally, and the verdict is in the top element.
* `counter_accepts_iff`: that top element is true (`castToBool`) exactly when at least two of
  the three equalities `s1 = c1`, `s2 = c2`, `s3 = c3` hold. `counter_accepts` states it for
  the result of `evalScript`: a truthy top element iff at least two slots match.
* `counter_repeat_rejects`: three EQUAL slots never reach the threshold, because the three
  constants are pairwise different. Repeats do not count twice, but two equal slots next to
  a third matching one can still reach it (for example `s1 = s2 = c1` and `s3 = c3`).
* `vectors_all8`: kernel-checked `verify` results for the eight locks that push the slots
  themselves (the model's `verify` runs against an empty unlocking script).

Not covered: `evalScript` with the slots as a real unlocking script in a spend (the model's
`verify` uses an empty one, so the `verify` check is on locks that push the slots); eras before
Genesis (`Good` requires after Genesis; `vectors/counter2of3-v1.json` also tests the
before-Genesis era, by comparison with the compiled node only).
-/

open Bsv.Interp Bsv.Splice Bsv.ScriptNum

namespace Bsv.Interp

/-- The state `s0` with a given main stack, alt stack and operation counter. -/
def S (s0 : State) (stk alt : Stack) (n : Nat) : State :=
  { s0 with stack := stk, alt := alt, ops := n }

theorem S_executing {s0 : State} (hb : Base s0) (stk alt : Stack) (n : Nat) :
    Executing (S s0 stk alt n) := by
  obtain ⟨h1, h2⟩ := hb
  simp [Executing, S, h1, h2]

theorem finOk_S {c : Cfg} (hG : Good c) {s0 : State} {stk alt : Stack} {n : Nat}
    (hf : Fits c stk) : finOk c (S s0 stk alt n) = true := by
  have h1 : c.p.afterGenesis = true := hG.ag
  simp only [finOk, S, h1, Bool.not_true, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
  intro e he
  exact Nat.not_lt.mpr (hf e he)

theorem runs_nil_S {c : Cfg} {s0 : State} (hb : Base s0) (stk alt : Stack) (n : Nat) :
    runs c [] (S s0 stk alt n) = .ok (S s0 stk alt n) :=
  runs_nil (c := c) (s0 := { s0 with alt := alt }) hb stk n

theorem runs_push_S {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {b : Byte}
    {d rest : List Byte} {stk alt : Stack} {n : Nat}
    (hlt : b.toNat < 0x4c) (hd : d.length = b.toNat) (hmin : minimalPush d b.toNat = true)
    (hmo : n ≤ c.maxOps) (hf : Fits c (d :: stk)) :
    runs c (b :: (d ++ rest)) (S s0 stk alt n) = runs c rest (S s0 (d :: stk) alt n) :=
  runs_push (s0 := { s0 with alt := alt }) hG hb hlt hd hmin hmo hf

/-- `runs_exec` for an opcode that may change the alt stack. -/
theorem runs_exec_S {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {b : Byte} {o : Nat}
    {rest : List Byte} {stk stk' alt alt' : Stack} {n n' : Nat} (hbo : b.toNat = o)
    (ho : 0x4e < o) (hnc : ¬(0x63 ≤ o ∧ o ≤ 0x68)) (h6a : o ≠ 0x6a)
    (hdis : o ≠ 0x8d ∧ o ≠ 0x8e)
    (hn' : (if 0x60 < o then n + 1 else n) = n') (hmo : n' ≤ c.maxOps)
    (hob : overBudget c o stk = false)
    (he : execOp c o stk alt = .ok (stk', alt')) (hf : Fits c stk') :
    runs c (b :: rest) (S s0 stk alt n) = runs c rest (S s0 stk' alt' n') := by
  subst hbo
  have hg : getOp (b :: rest) = some (b.toNat, [], rest) := getOp_op ho
  have hops : opsAfter (S s0 stk alt n) b.toNat = n' := by
    simp only [opsAfter, S]; exact hn'
  have hs := step_plain (c := c) (s := S s0 stk alt n) (o := b.toNat) (st := stk') (alt := alt')
    (S_executing hb stk alt n) ho hnc h6a (by rw [hops]; exact hmo)
    (fun h => by
      rcases h with h | h
      · exact absurd h hdis.1
      · exact absurd h hdis.2) hob
    (by simpa [S] using he)
    (by rw [hops]; exact finOk_S hG hf)
  rw [runs_cons hg (s' := S s0 stk' alt' n') (by rw [hs, hops]; rfl)]

/-! ### Two more single-opcode effects -/

section ExecOp
variable (c : Cfg) (alt : Stack)

theorem execOp_add (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) (hl : (encInt (a + b)).length ≤ c.p.maxNumLen) :
    execOp c 0x93 (x2 :: x1 :: r) alt = .ok (encInt (a + b) :: r, alt) := by
  have hn : ¬ ((encInt (a + b)).length > c.p.maxNumLen) := Nat.not_lt.mpr hl
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, pushChecked, hn, liftE,
    Except.map]

theorem execOp_ge (x2 x1 : Elem) (r : Stack) (a b : Int) (h1 : num c.p x1 = .ok a)
    (h2 : num c.p x2 = .ok b) :
    execOp c 0xa2 (x2 :: x1 :: r) alt = .ok (encInt (boolInt (decide (a ≥ b))) :: r, alt) := by
  simp [execOp, modelled, unaryOf, binaryOf, opBinary, h1, h2, liftE, Except.map]

end ExecOp

/-! ### Small numbers -/

theorem enc0 : encInt 0 = ([] : Elem) := by decide
theorem enc1 : encInt 1 = [1#8] := by decide
theorem enc2 : encInt 2 = [2#8] := by decide
theorem enc3 : encInt 3 = [3#8] := by decide

theorem enc_len_small (t : Int) (h0 : 0 ≤ t) (h3 : t ≤ 3) : (encInt t).length ≤ 1 := by
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · rw [enc0]; decide
  · rw [enc1]; decide
  · rw [enc2]; decide
  · rw [enc3]; decide

theorem boolInt_nonneg (b : Bool) : 0 ≤ boolInt b := by cases b <;> simp [boolInt]
theorem boolInt_le_one (b : Bool) : boolInt b ≤ 1 := by cases b <;> simp [boolInt]

theorem eq_elem (x d : Elem) : (if x == d then [1#8] else []) = encInt (boolInt (x == d)) := by
  by_cases h : (x == d) = true
  · simp [h, boolInt, enc1]
  · simp [h, boolInt, enc0]

/-! ### One slot -/

/-- The four bytes `c1c1`, `c2c2`, `c3c3`. -/
def k1 : Elem := [0x63#8, 0x31#8, 0x63#8, 0x31#8]
def k2 : Elem := [0x63#8, 0x32#8, 0x63#8, 0x32#8]
def k3 : Elem := [0x63#8, 0x33#8, 0x63#8, 0x33#8]

/-- `<k> OP_EQUAL OP_FROMALTSTACK OP_ADD OP_TOALTSTACK`. -/
def blk (k : Elem) : List Byte := 0x04#8 :: (k ++ [0x87#8, 0x6c#8, 0x93#8, 0x6b#8])

/-- One slot: compare `x` with `k`, add the result to the tally `t` on the alt stack. -/
theorem blk_runs {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {k x : Elem}
    (hk : k.length = 4) (hkm : minimalPush k 4 = true)
    {rest : List Byte} {stk : Stack} {t : Int} {n : Nat}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (hmo : n + 4 ≤ c.maxOps) (hf : Fits c (x :: stk)) :
    runs c (blk k ++ rest) (S s0 (x :: stk) [encInt t] n)
      = runs c rest (S s0 stk [encInt (boolInt (x == k) + t)] (n + 4)) := by
  have hbud : 75 ≤ c.budget := hG.bud
  have hag : c.p.afterGenesis = true := hG.ag
  have hmnl : 1 ≤ c.p.maxNumLen := hG.mnl
  have hxf := (Fits_cons c x stk).mp hf
  have hkf : k.length ≤ c.budget := by omega
  have hbt := boolInt_nonneg (x == k)
  have hbl := boolInt_le_one (x == k)
  have hlt : (encInt t).length ≤ c.p.maxNumLen := by
    have := enc_len_small t ht0 (by omega); omega
  have hls : (encInt (boolInt (x == k) + t)).length ≤ c.p.maxNumLen := by
    have := enc_len_small (boolInt (x == k) + t) (by omega) (by omega); omega
  have hle : (encInt (boolInt (x == k))).length ≤ c.p.maxNumLen := by
    have := enc_len_small (boolInt (x == k)) hbt (by omega); omega
  have hnb : num c.p (encInt (boolInt (x == k))) = .ok (boolInt (x == k)) := num_encInt _ hag hle
  have hnt : num c.p (encInt t) = .ok t := num_encInt _ hag hlt
  unfold blk
  rw [List.cons_append, List.append_assoc]
  -- the push
  rw [runs_push_S hG hb (d := k) (b := 0x04#8) (by decide) (by simpa using hk) (by simpa using hkm)
    (by omega) ((Fits_cons c k (x :: stk)).mpr ⟨hkf, hf⟩)]
  simp only [List.cons_append, List.nil_append]
  -- OP_EQUAL
  have hfe : Fits c ((if x == k then [1#8] else []) :: stk) := by
    rw [Fits_cons]; refine ⟨?_, hxf.2⟩
    by_cases h : (x == k) = true <;> simp [h] <;> omega
  rw [runs_exec_S hG hb (b := 0x87#8) (o := 0x87) (n := n) (n' := n + 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by split <;> omega) (by omega) (by simp [overBudget]) (execOp_equal c [encInt t] k x stk) hfe]
  -- OP_FROMALTSTACK
  have hff : Fits c (encInt t :: (if x == k then [1#8] else []) :: stk) := by
    rw [Fits_cons]; refine ⟨by have := enc_len_small t ht0 (by omega); omega, hfe⟩
  rw [runs_exec_S hG hb (b := 0x6c#8) (o := 0x6c) (n := n + 1) (n' := n + 2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by split <;> omega) (by omega) (by simp [overBudget])
    (execOp_fromalt c (encInt t) [] ((if x == k then [1#8] else []) :: stk)) hff]
  -- OP_ADD
  rw [eq_elem] at hff ⊢
  have hfa : Fits c (encInt (boolInt (x == k) + t) :: stk) := by
    rw [Fits_cons]; exact ⟨by have := enc_len_small (boolInt (x == k) + t) (by omega) (by omega); omega, hxf.2⟩
  rw [runs_exec_S hG hb (b := 0x93#8) (o := 0x93) (n := n + 2) (n' := n + 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by split <;> omega) (by omega) (by simp [overBudget])
    (execOp_add c [] (encInt t) (encInt (boolInt (x == k))) stk (boolInt (x == k)) t hnb hnt hls)
    hfa]
  -- OP_TOALTSTACK
  rw [runs_exec_S hG hb (b := 0x6b#8) (o := 0x6b) (n := n + 3) (n' := n + 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by split <;> omega) (by omega) (by simp [overBudget])
    (execOp_toalt c [] (encInt (boolInt (x == k) + t)) stk) hxf.2]

/-! ### The whole script -/

/-- `0 OP_TOALTSTACK`, three slots, `OP_FROMALTSTACK OP_2 OP_GREATERTHANOREQUAL`. -/
def counter : List Byte :=
  0x00#8 :: 0x6b#8 :: (blk k3 ++ (blk k2 ++ (blk k1 ++ [0x6c#8, 0x52#8, 0xa2#8])))

/-- The 32 bytes of the script as sent: `006b0463336333876c936b...6c52a2`. -/
theorem counter_bytes :
    counter.map (·.toNat) =
      [0x00, 0x6b, 0x04, 0x63, 0x33, 0x63, 0x33, 0x87, 0x6c, 0x93, 0x6b,
       0x04, 0x63, 0x32, 0x63, 0x32, 0x87, 0x6c, 0x93, 0x6b,
       0x04, 0x63, 0x31, 0x63, 0x31, 0x87, 0x6c, 0x93, 0x6b, 0x6c, 0x52, 0xa2] := by decide

theorem counter_length : counter.length = 32 := by decide

/-- The number of slots equal to their own constant. -/
def count (s1 s2 s3 : Elem) : Int :=
  boolInt (s1 == k1) + boolInt (s2 == k2) + boolInt (s3 == k3)

theorem counter_runs {c : Cfg} (hG : Good c) {s0 : State} (hb : Base s0) {s1 s2 s3 : Elem}
    {r : Stack} {n : Nat} (hmo : n + 15 ≤ c.maxOps) (hf : Fits c (s3 :: s2 :: s1 :: r)) :
    runs c counter (S s0 (s3 :: s2 :: s1 :: r) [] n)
      = .ok (S s0 (encInt (boolInt (decide (count s1 s2 s3 ≥ 2))) :: r) [] (n + 15)) := by
  have hbud : 75 ≤ c.budget := hG.bud
  have hag : c.p.afterGenesis = true := hG.ag
  have hmnl : 1 ≤ c.p.maxNumLen := hG.mnl
  obtain ⟨h3, hf2⟩ := (Fits_cons c s3 _).mp hf
  obtain ⟨h2, hf1⟩ := (Fits_cons c s2 _).mp hf2
  obtain ⟨h1, hr''⟩ := (Fits_cons c s1 r).mp hf1
  have hb1 := boolInt_nonneg (s1 == k1)
  have hb2 := boolInt_nonneg (s2 == k2)
  have hb3 := boolInt_nonneg (s3 == k3)
  have hu1 := boolInt_le_one (s1 == k1)
  have hu2 := boolInt_le_one (s2 == k2)
  have hu3 := boolInt_le_one (s3 == k3)
  unfold counter
  -- 0
  have hp := runs_push_S hG hb (b := 0x00#8) (d := []) (stk := s3 :: s2 :: s1 :: r) (alt := [])
    (n := n) (rest := 0x6b#8 :: (blk k3 ++ (blk k2 ++ (blk k1 ++ [0x6c#8, 0x52#8, 0xa2#8]))))
    (by decide) (by decide) (by decide) (by omega) ((Fits_cons c [] _).mpr ⟨by simp only [List.length_nil]; omega, hf⟩)
  simp only [List.nil_append] at hp
  rw [hp]
  -- OP_TOALTSTACK
  rw [runs_exec_S hG hb (b := 0x6b#8) (o := 0x6b) (n := n) (n' := n + 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by split <;> omega) (by omega) (by simp [overBudget])
    (execOp_toalt c [] ([] : Elem) (s3 :: s2 :: s1 :: r)) hf]
  rw [show ([] :: ([] : Stack)) = [encInt 0] by rw [enc0]]
  -- the three slots
  rw [blk_runs hG hb (x := s3) (stk := s2 :: s1 :: r) (t := 0) (n := n + 1) (by decide)
    (by decide) (by omega) (by omega) (by omega) hf]
  rw [blk_runs hG hb (x := s2) (stk := s1 :: r) (t := boolInt (s3 == k3) + 0) (n := n + 1 + 4)
    (by decide) (by decide) (by omega) (by omega) (by omega) hf2]
  rw [blk_runs hG hb (x := s1) (stk := r) (t := boolInt (s2 == k2) + (boolInt (s3 == k3) + 0))
    (n := n + 1 + 4 + 4) (by decide) (by decide) (by omega) (by omega) (by omega) hf1]
  have hT : boolInt (s1 == k1) + (boolInt (s2 == k2) + (boolInt (s3 == k3) + 0))
      = count s1 s2 s3 := by unfold count; omega
  have hT0 : 0 ≤ count s1 s2 s3 := by unfold count; omega
  have hT3 : count s1 s2 s3 ≤ 3 := by unfold count; omega
  rw [hT]
  have hl : (encInt (count s1 s2 s3)).length ≤ 1 := enc_len_small _ hT0 hT3
  have hnT : num c.p (encInt (count s1 s2 s3)) = .ok (count s1 s2 s3) :=
    num_encInt _ hag (by omega)
  have hfT : Fits c (encInt (count s1 s2 s3) :: r) := (Fits_cons c _ r).mpr ⟨by omega, hr''⟩
  -- OP_FROMALTSTACK
  rw [runs_exec_S hG hb (b := 0x6c#8) (o := 0x6c) (n := n + 1 + 4 + 4 + 4) (n' := n + 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by split <;> omega) (by omega)
    (by simp [overBudget]) (execOp_fromalt c (encInt (count s1 s2 s3)) [] r) hfT]
  -- OP_2
  have h2e : (encInt 2).length ≤ 1 := enc_len_small 2 (by omega) (by omega)
  have hf2' : Fits c (encInt 2 :: encInt (count s1 s2 s3) :: r) :=
    (Fits_cons c _ _).mpr ⟨by omega, hfT⟩
  have hx2 : execOp c 0x52 (encInt (count s1 s2 s3) :: r) [] =
      .ok (encInt 2 :: encInt (count s1 s2 s3) :: r, []) := by
    have := execOp_small c [] 0x52 (by decide) (by decide) (encInt (count s1 s2 s3) :: r)
    exact this
  rw [runs_exec_S hG hb (b := 0x52#8) (o := 0x52) (n := n + 14) (n' := n + 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by split <;> omega) (by omega)
    (by simp [overBudget]) hx2 hf2']
  -- OP_GREATERTHANOREQUAL
  have hn2 : num c.p (encInt 2) = .ok 2 := num_encInt _ hag (by omega)
  have hfg : Fits c (encInt (boolInt (decide (count s1 s2 s3 ≥ 2))) :: r) := by
    have := enc_len_small (boolInt (decide (count s1 s2 s3 ≥ 2)))
      (boolInt_nonneg _) (by have := boolInt_le_one (decide (count s1 s2 s3 ≥ 2)); omega)
    exact (Fits_cons c _ r).mpr ⟨by omega, hr''⟩
  rw [runs_exec_S hG hb (b := 0xa2#8) (o := 0xa2) (n := n + 14) (n' := n + 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by split <;> omega) (by omega)
    (by simp [overBudget])
    (execOp_ge c [] (encInt 2) (encInt (count s1 s2 s3)) r (count s1 s2 s3) 2 hnT hn2) hfg]
  exact runs_nil_S hb _ _ _

/-- `EvalScript` on the three slots as the starting stack (`s3` on top). -/
theorem counter_evalScript {c : Cfg} (hG : Good c) (hflags : c.flagsValid = true)
    (hsz : 32 ≤ c.maxScriptSize) (hmo : 15 ≤ c.maxOps) {s1 s2 s3 : Elem}
    (hf : Fits c [s3, s2, s1]) :
    evalScript c counter [s3, s2, s1]
      = .ok [encInt (boolInt (decide (count s1 s2 s3 ≥ 2)))] := by
  have h := counter_runs hG (s0 := ({} : State)) ⟨rfl, rfl⟩ (s1 := s1) (s2 := s2) (s3 := s3)
    (r := []) (n := 0) (by omega) hf
  have h1 : (!c.flagsValid) = false := by simp [hflags]
  have h2 : ¬ (counter.length > c.maxScriptSize) := by
    rw [counter_length]; omega
  unfold evalScript
  rw [h1, if_neg (by simp), if_neg h2]
  exact congrArg (Except.map (·.stack)) h

theorem castToBool_boolInt (b : Bool) : castToBool (encInt (boolInt b)) = b := by
  cases b
  · simp [boolInt, enc0, castToBool]
  · simp [boolInt, enc1, castToBool]

theorem two_of_three (e1 e2 e3 : Bool) :
    decide (boolInt e1 + boolInt e2 + boolInt e3 ≥ 2) = ((e1 && e2) || (e1 && e3) || (e2 && e3)) := by
  cases e1 <;> cases e2 <;> cases e3 <;> decide

/-- The final element is true exactly when at least two slots equal their own constant. -/
theorem counter_accepts_iff (s1 s2 s3 : Elem) :
    castToBool (encInt (boolInt (decide (count s1 s2 s3 ≥ 2)))) = true
      ↔ (((s1 == k1) && (s2 == k2)) || ((s1 == k1) && (s3 == k3)) || ((s2 == k2) && (s3 == k3)))
          = true := by
  rw [castToBool_boolInt]
  unfold count
  rw [two_of_three]

/-- Running the script on the slots leaves a truthy top element iff at least two slots match. -/
theorem counter_accepts {c : Cfg} (hG : Good c) (hflags : c.flagsValid = true)
    (hsz : 32 ≤ c.maxScriptSize) (hmo : 15 ≤ c.maxOps) {s1 s2 s3 : Elem}
    (hf : Fits c [s3, s2, s1]) :
    (match evalScript c counter [s3, s2, s1] with
      | .ok (top :: _) => castToBool top
      | _ => false) = true
      ↔ (((s1 == k1) && (s2 == k2)) || ((s1 == k1) && (s3 == k3)) || ((s2 == k2) && (s3 == k3)))
          = true := by
  rw [counter_evalScript hG hflags hsz hmo hf]
  exact counter_accepts_iff s1 s2 s3

theorem both_false {a b : Elem} (hab : (a == b) = false) (v : Elem) : (v == a && v == b) = false := by
  cases h : (v == a)
  · rfl
  · have := beq_iff_eq.mp h
    subst this
    simpa using hab

/-- Three equal slots never reach the threshold: the constants are pairwise different. -/
theorem counter_repeat_rejects (v : Elem) : decide (count v v v ≥ 2) = false := by
  unfold count
  rw [two_of_three]
  have d12 := both_false (a := k1) (b := k2) (by decide) v
  have d13 := both_false (a := k1) (b := k3) (by decide) v
  have d23 := both_false (a := k2) (b := k3) (by decide) v
  rw [d12, d13, d23]
  rfl

/-! ### The model's `verify`, which runs against an empty unlocking script

The slots are pushed by a prefix of the lock. A slot is either its own constant (`true`) or
`OP_0` (`false`). The flag word is the after-Genesis word of `vectors/stack1000-v1.json`. -/

def slotScript (b : Bool) (k : Elem) : List Byte := if b then 0x04#8 :: k else [0x00#8]

def fullScript (a b c : Bool) : List Byte :=
  slotScript a k1 ++ slotScript b k2 ++ slotScript c k3 ++ counter

def flagsGenesis : Nat := 1402863 ||| (1 <<< 19)

theorem vectors_all8 : ∀ a b c : Bool,
    verify (cfgOf 1 flagsGenesis) (fullScript a b c)
      = (if ((a && b) || (a && c) || (b && c)) = true then none else some .evalFalse) := by
  decide

end Bsv.Interp
