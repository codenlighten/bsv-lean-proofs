import BsvLeanProofs.Arith

/-!
# Reference semantics, slice 5: the interpreter loop

Whole scripts: instruction decoding, the minimal-push rule, conditionals,
OP_VERIFY and OP_RETURN, the stack and alt-stack opcodes, OP_EQUAL and the
bitwise opcodes, and every opcode of slices 1 to 4, composed as
`EvalScript` composes them, followed by `VerifyScript`'s final checks.
Written from bitcoin-sv v1.2.3, `src/script/interpreter.cpp` (`EvalScript`,
`VerifyScript`) and `script.h` (`GetOp2`).

Scope. One script, run as the locking script against an empty unlocking
script. NOT modelled, and reported as `outOfModel` if a script executes them:
the hash and signature opcodes, and OP_CHECKLOCKTIMEVERIFY /
OP_CHECKSEQUENCEVERIFY where they are active (before Genesis). Also not
modelled: pay-to-script-hash evaluation (its pattern starts with a hash
opcode), the stack-memory limit, and elements above `budget` bytes, which are
reported as `outOfModel` so that the model never has to build them.

This file has no theorems about the loop. Its evidence is differential: random
scripts on which a compiled node returns the same verdict (`difftest/`).
-/

namespace Bsv.Interp

open Bsv.ScriptNum Bsv.Splice

inductive IErr
  | op (e : Err)
  | bigInt
  | badOpcode
  | unbalancedConditional
  | verify
  | equalVerify
  | opReturn
  | opCount
  | scriptSize
  | stackSize
  | minimalData
  | minimalIf
  | invalidAltstackOperation
  | invalidOperandSize
  | evalFalse
  | cleanStack
  | invalidFlags
  | outOfModel
  deriving DecidableEq, Repr

/-- What the flag word, the transaction version and the limits fix. -/
structure Cfg where
  p : Params
  minimalIf : Bool
  cleanStack : Bool
  cltv : Bool
  csv : Bool
  txVersion : Nat
  maxOps : Nat
  maxScriptSize : Nat
  /-- The flag word is one `EvalScript` accepts: not "after Chronicle" without
  "after Genesis". -/
  flagsValid : Bool := true
  /-- CLEANSTACK is set without P2SH, which `VerifyScript` refuses at the end. -/
  cleanStackNoP2SH : Bool := false
  budget : Nat := 4096

/-- The configuration `VerifyScript` derives from a flag word (`script_flags.h`
bit numbers) and the spending transaction's version, with consensus limits.
Non-malleability rules (minimal encodings, MINIMALIF, CLEANSTACK) are not
enforced once Chronicle is active and the version is above 1. -/
def cfgOf (version flags : Nat) : Cfg :=
  let bit (i : Nat) := flags.testBit i
  let enforce := !(bit 20 && decide (version > 1))
  let ag := bit 19
  let ac := bit 21
  { p := { requireMinimal := bit 6 && enforce,
           maxNumLen := if ac then 32000000 else if ag then 750000 else 4,
           afterGenesis := ag, chronicleOps := ac, discourageNops := bit 7 },
    minimalIf := bit 13 && enforce, cleanStack := bit 8 && enforce,
    cltv := bit 9, csv := bit 10, txVersion := version,
    maxOps := if ag then 4294967295 else 500,
    maxScriptSize := if ag then 4294967295 else 10000,
    flagsValid := !(ac && !ag), cleanStackNoP2SH := bit 8 && !bit 0 }

structure State where
  stack : Stack := []
  alt : Stack := []
  /-- Open conditionals, innermost first: (branch is taken, OP_ELSE seen). -/
  conds : List (Bool × Bool) := []
  ops : Nat := 0
  /-- OP_RETURN was executed inside a conditional (after Genesis). -/
  ret : Bool := false

/-- `CastToBool`: false for all-zero strings and for negative zero. -/
def castToBool : Elem → Bool
  | [] => false
  | [b] => b != 0#8 && b != 0x80#8
  | b :: c :: rest => b != 0#8 || castToBool (c :: rest)

def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

def le4 (n : Nat) : Elem :=
  [BitVec.ofNat 8 n, BitVec.ofNat 8 (n / 256), BitVec.ofNat 8 (n / 65536), BitVec.ofNat 8 (n / 16777216)]

/-- `GetOp2`: the opcode, its push data, and the rest of the script. -/
def getOp : List Byte → Option (Nat × Elem × List Byte)
  | [] => none
  | b :: rest =>
    let o := b.toNat
    if o > 0x4e then some (o, [], rest)
    else
      let hdr := if o < 0x4c then 0 else if o == 0x4c then 1 else if o == 0x4d then 2 else 4
      if rest.length < hdr then none
      else
        let n := if o < 0x4c then o else leNat (rest.take hdr)
        let body := rest.drop hdr
        if body.length < n then none else some (o, body.take n, body.drop n)

/-- `CheckMinimalPush`. -/
def minimalPush (d : Elem) (o : Nat) : Bool :=
  match d with
  | [] => o == 0
  | [b] =>
    if 1 ≤ b.toNat ∧ b.toNat ≤ 16 then o == 0x50 + b.toNat
    else if b.toNat = 0x81 then o == 0x4f
    else o == 1
  | _ =>
    if d.length ≤ 75 then o == d.length
    else if d.length ≤ 255 then o == 0x4c
    else if d.length ≤ 65535 then o == 0x4d
    else true

def liftE : Except Err Stack → Except IErr Stack
  | .ok s => .ok s
  | .error e => .error (.op e)

def liftS : Except ShiftErr Stack → Except IErr Stack
  | .ok s => .ok s
  | .error (.base e) => .error (.op e)
  | .error .bigInt => .error .bigInt

def unaryOf : Nat → Option Unary
  | 0x8b => some .add1 | 0x8c => some .sub1 | 0x8d => some .mul2 | 0x8e => some .div2
  | 0x8f => some .negate | 0x90 => some .abs | 0x91 => some .not | 0x92 => some .notEqual0
  | _ => none

def binaryOf : Nat → Option Binary
  | 0x93 => some .add | 0x94 => some .sub | 0x95 => some .mul | 0x96 => some .div
  | 0x97 => some .mod | 0x9a => some .boolAnd | 0x9b => some .boolOr | 0x9c => some .numEqual
  | 0x9d => some .numEqualVerify | 0x9e => some .numNotEqual | 0x9f => some .lt
  | 0xa0 => some .gt | 0xa1 => some .le | 0xa2 => some .ge | 0xa3 => some .min
  | 0xa4 => some .max
  | _ => none

/-- The opcodes of the earlier slices, by opcode byte. -/
def modelled (c : Cfg) (o : Nat) (st : Stack) : Option (Except IErr Stack) :=
  let p := c.p
  if o = 0x7e then some (liftE (opCat p st))
  else if o = 0x7f then some (liftE (opSplit p st))
  else if o = 0x80 then some (liftE (opNum2Bin p st))
  else if o = 0x81 then some (liftE (opBin2Num p st))
  else if o = 0x82 then some (liftE (opSize p st))
  else if o = 0x98 then some (liftE (opLShift p st))
  else if o = 0x99 then some (liftE (opRShift p st))
  else if o = 0xa5 then some (liftE (opWithin p st))
  else if o = 0xb3 then some (liftE (chronicleGate p opSubstr st))
  else if o = 0xb4 then some (liftE (chronicleGate p opLeft st))
  else if o = 0xb5 then some (liftE (chronicleGate p opRight st))
  else if o = 0xb6 then some (liftS (chronicleGateS p opLShiftNum st))
  else if o = 0xb7 then some (liftS (chronicleGateS p opRShiftNum st))
  else match unaryOf o with
    | some u => some (liftE (opUnary u p st))
    | none => match binaryOf o with
      | some b => some (liftE (opBinary b p st))
      | none => none

def bitwise (f : Byte → Byte → Byte) (alt : Stack) : Stack → Except IErr (Stack × Stack)
  | b :: a :: r =>
    if a.length ≠ b.length then .error .invalidOperandSize
    else .ok (List.zipWith f a b :: r, alt)
  | _ => .error (.op .invalidStackOperation)

/-- One executed opcode other than a push, a conditional or OP_RETURN. The
stack lists have the top element first. -/
def execOp (c : Cfg) (o : Nat) (st alt : Stack) : Except IErr (Stack × Stack) :=
  let p := c.p
  let bad : Except IErr (Stack × Stack) := .error (.op .invalidStackOperation)
  let nop : Except IErr (Stack × Stack) :=
    if p.discourageNops then .error (.op .discourageUpgradableNops) else .ok (st, alt)
  if o = 0x4f then .ok (encInt (-1) :: st, alt)
  else if 0x51 ≤ o ∧ o ≤ 0x60 then .ok (encInt (Int.ofNat (o - 0x50)) :: st, alt)
  else if o = 0x61 ∨ o = 0xab then .ok (st, alt)
  else if o = 0x62 then
    if p.chronicleOps then .ok (le4 c.txVersion :: st, alt) else .error .badOpcode
  else if o = 0xb0 ∨ o = 0xb8 ∨ o = 0xb9 then nop
  else if o = 0xb1 then (if !c.cltv || p.afterGenesis then nop else .error .outOfModel)
  else if o = 0xb2 then (if !c.csv || p.afterGenesis then nop else .error .outOfModel)
  else if o = 0x69 then
    match st with
    | x :: r => if castToBool x then .ok (r, alt) else .error .verify
    | _ => bad
  else if o = 0x6b then (match st with | x :: r => .ok (r, x :: alt) | _ => bad)
  else if o = 0x6c then
    match alt with
    | x :: r => .ok (x :: st, r)
    | _ => .error .invalidAltstackOperation
  else if o = 0x6d then (match st with | _ :: _ :: r => .ok (r, alt) | _ => bad)
  else if o = 0x6e then (match st with | a :: b :: r => .ok (a :: b :: a :: b :: r, alt) | _ => bad)
  else if o = 0x6f then
    match st with
    | a :: b :: d :: r => .ok (a :: b :: d :: a :: b :: d :: r, alt)
    | _ => bad
  else if o = 0x70 then
    match st with
    | a :: b :: d :: e :: r => .ok (d :: e :: a :: b :: d :: e :: r, alt)
    | _ => bad
  else if o = 0x71 then
    match st with
    | x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: r => .ok (x2 :: x1 :: x6 :: x5 :: x4 :: x3 :: r, alt)
    | _ => bad
  else if o = 0x72 then
    match st with
    | x4 :: x3 :: x2 :: x1 :: r => .ok (x2 :: x1 :: x4 :: x3 :: r, alt)
    | _ => bad
  else if o = 0x73 then
    match st with
    | x :: r => .ok (if castToBool x then x :: x :: r else x :: r, alt)
    | _ => bad
  else if o = 0x74 then .ok (encNat st.length :: st, alt)
  else if o = 0x75 then (match st with | _ :: r => .ok (r, alt) | _ => bad)
  else if o = 0x76 then (match st with | x :: r => .ok (x :: x :: r, alt) | _ => bad)
  else if o = 0x77 then (match st with | a :: _ :: r => .ok (a :: r, alt) | _ => bad)
  else if o = 0x78 then (match st with | a :: b :: r => .ok (b :: a :: b :: r, alt) | _ => bad)
  else if o = 0x79 ∨ o = 0x7a then
    match st with
    | n :: x :: r =>
      let rest := x :: r
      match num p n with
      | .error e => .error (.op e)
      | .ok v =>
        if v < 0 ∨ v ≥ rest.length then bad
        else
          let i := v.toNat
          let e := rest.getD i []
          .ok (if o = 0x7a then e :: rest.eraseIdx i else e :: rest, alt)
    | _ => bad
  else if o = 0x7b then (match st with | x3 :: x2 :: x1 :: r => .ok (x1 :: x3 :: x2 :: r, alt) | _ => bad)
  else if o = 0x7c then (match st with | a :: b :: r => .ok (b :: a :: r, alt) | _ => bad)
  else if o = 0x7d then (match st with | a :: b :: r => .ok (a :: b :: a :: r, alt) | _ => bad)
  else if o = 0x83 then (match st with | x :: r => .ok (x.map (~~~ ·) :: r, alt) | _ => bad)
  else if o = 0x84 then bitwise (· &&& ·) alt st
  else if o = 0x85 then bitwise (· ||| ·) alt st
  else if o = 0x86 then bitwise (· ^^^ ·) alt st
  else if o = 0x87 then
    match st with
    | b :: a :: r => .ok ((if a == b then [1#8] else []) :: r, alt)
    | _ => bad
  else if o = 0x88 then
    match st with
    | b :: a :: r => if a == b then .ok (r, alt) else .error .equalVerify
    | _ => bad
  else if 0xa6 ≤ o ∧ o ≤ 0xaf then .error .outOfModel
  else match modelled c o st with
    | some r => r.map (·, alt)
    | none => .error .badOpcode

inductive Out
  | cont (s : State)
  | done (s : State)
  | err (e : IErr)

/-- The model does not build elements above the budget: scripts that would are
set aside, not judged. OP_RSHIFTNUM is included although its result is small,
because the model computes it by dividing by a power of two it would have to
build; large counts for it are covered by the curated shift vectors. -/
def overBudget (c : Cfg) (o : Nat) (st : Stack) : Bool :=
  ((o = 0x80 ∨ o = 0xb6 ∨ o = 0xb7) && (o = 0x80 || c.p.chronicleOps)) &&
  match st with
  | n :: _ => match num c.p n with
    | .ok v => decide (v > 8 * c.budget)
    | .error _ => false
  | [] => false

/-- One instruction, in the order `EvalScript` applies its checks. -/
def step (c : Cfg) (s : State) (o : Nat) (d : Elem) : Out :=
  let p := c.p
  if !p.afterGenesis && decide (d.length > 520) then .err (.op .pushSize) else
  let active := s.conds.all (·.1)
  let fExec := active && (!s.ret || o == 0x6a)
  let ops := if o > 0x60 then s.ops + 1 else s.ops
  if ops > c.maxOps then .err .opCount else
  if (o == 0x8d || o == 0x8e) && !p.chronicleOps && (!p.afterGenesis || fExec) then
    .err (.op .disabledOpcode) else
  let s := { s with ops := ops }
  let fin (s : State) : Out :=
    if !p.afterGenesis && decide (s.stack.length + s.alt.length > 1000) then .err .stackSize
    else if s.stack.any (fun e => decide (e.length > c.budget)) then .err .outOfModel
    else .cont s
  if fExec && decide (o ≤ 0x4e) then
    if p.requireMinimal && !minimalPush d o then .err .minimalData
    else fin { s with stack := d :: s.stack }
  else if fExec || (decide (0x63 ≤ o) && decide (o ≤ 0x68)) then
    if o == 0x63 || o == 0x64 || o == 0x65 || o == 0x66 then
      if (o == 0x65 || o == 0x66) && !p.chronicleOps then
        if p.afterGenesis && !fExec then fin s else .err .badOpcode
      else if fExec then
        match s.stack with
        | [] => .err .unbalancedConditional
        | v :: r =>
          if (o == 0x63 || o == 0x64) && c.minimalIf &&
              (decide (v.length > 1) || (v.length == 1 && v != [1#8])) then .err .minimalIf
          else
            let f0 := if o == 0x65 || o == 0x66 then v == le4 c.txVersion else castToBool v
            let f := if o == 0x64 || o == 0x66 then !f0 else f0
            fin { s with stack := r, conds := (f, false) :: s.conds }
      else fin { s with conds := (false, false) :: s.conds }
    else if o == 0x67 then
      match s.conds with
      | [] => .err .unbalancedConditional
      | (b, e) :: r =>
        if e && p.afterGenesis then .err .unbalancedConditional
        else fin { s with conds := (!b, true) :: r }
    else if o == 0x68 then
      match s.conds with
      | [] => .err .unbalancedConditional
      | _ :: r => fin { s with conds := r }
    else if o == 0x6a then
      if p.afterGenesis then (if s.conds.isEmpty then .done s else fin { s with ret := true })
      else .err .opReturn
    else if overBudget c o s.stack then .err .outOfModel
    else
      match execOp c o s.stack s.alt with
      | .error e => .err e
      | .ok (st, alt) => fin { s with stack := st, alt := alt }
  else fin s

def run (c : Cfg) : Nat → List Byte → State → Except IErr State
  | 0, _, s => .ok s
  | fuel + 1, script, s =>
    if script.isEmpty then
      (if s.conds.isEmpty then .ok s else .error .unbalancedConditional)
    else match getOp script with
      | none => .error .badOpcode
      | some (o, d, rest) =>
        match step c s o d with
        | .err e => .error e
        | .done s => .ok s
        | .cont s => run c fuel rest s

/-- `EvalScript` on a starting stack. -/
def evalScript (c : Cfg) (script : List Byte) (st : Stack) : Except IErr Stack :=
  if !c.flagsValid then .error .invalidFlags
  else if script.length > c.maxScriptSize then .error .scriptSize
  else (run c (script.length + 1) script { stack := st }).map (·.stack)

/-- `VerifyScript` for an empty unlocking script: `none` is acceptance. -/
def verify (c : Cfg) (script : List Byte) : Option IErr :=
  match evalScript c script [] with
  | .error e => some e
  | .ok st =>
    match st with
    | [] => some .evalFalse
    | top :: _ =>
      if !castToBool top then some .evalFalse
      else if c.cleanStackNoP2SH then some .invalidFlags
      else if c.cleanStack && st.length != 1 then some .cleanStack
      else none

end Bsv.Interp
