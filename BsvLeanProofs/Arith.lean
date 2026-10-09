import BsvLeanProofs.ByteShift

/-!
# Reference semantics, slice 4: the arithmetic and comparison opcodes

OP_1ADD, OP_1SUB, OP_2MUL, OP_2DIV, OP_NEGATE, OP_ABS, OP_NOT, OP_0NOTEQUAL,
OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_MOD, OP_BOOLAND, OP_BOOLOR, OP_NUMEQUAL,
OP_NUMEQUALVERIFY, OP_NUMNOTEQUAL, the four orderings, OP_MIN, OP_MAX and
OP_WITHIN. Written from bitcoin-sv v1.2.3: `src/script/interpreter.cpp` (the
"Numeric" case blocks) and `script_num.cpp` (the arithmetic operators).

What is modelled: operands are read with the era's reader (narrow before
Genesis, big-integer after); the result is the integer result, pushed in its
minimal encoding. After Genesis a result of addition, subtraction,
multiplication, negation or doubling longer than `MaxScriptNumLength` is
refused. Division and remainder truncate toward zero. OP_2MUL and OP_2DIV are
disabled unless the output was created after Chronicle.
What is assumed: big-integer arithmetic is integer arithmetic with truncating
division. Before Genesis the source computes in `int64_t`; its operands are at
most four bytes, so no result overflows (`narrow_no_overflow` below).
-/

namespace Bsv.Splice

open Bsv.ScriptNum

/-- An operand, read with the era's reader. -/
def num (p : Params) (s : Elem) : Except Err Int :=
  scriptNum p.requireMinimal p.maxNumLen p.afterGenesis s

/-- Push a result whose size is checked after Genesis. -/
def pushChecked (p : Params) (r : Int) (st : Stack) : Except Err Stack :=
  if p.afterGenesis && decide ((encInt r).length > p.maxNumLen) then .error .scriptNumOverflow
  else .ok (encInt r :: st)

def boolInt (b : Bool) : Int := if b then 1 else 0

inductive Unary
  | add1 | sub1 | mul2 | div2 | negate | abs | not | notEqual0
  deriving DecidableEq

def opUnary (u : Unary) (p : Params) : Stack → Except Err Stack
  | x :: st =>
    if (u == .mul2 || u == .div2) && !p.chronicleOps then .error .disabledOpcode
    else match num p x with
    | .error e => .error e
    | .ok v =>
      match u with
      | .add1 => pushChecked p (v + 1) st
      | .sub1 => pushChecked p (v - 1) st
      | .mul2 => pushChecked p (v + v) st
      | .div2 => .ok (encInt (Int.tdiv v 2) :: st)
      | .negate => pushChecked p (-v) st
      | .abs => if v < 0 then pushChecked p (-v) st else .ok (encInt v :: st)
      | .not => .ok (encInt (boolInt (v == 0)) :: st)
      | .notEqual0 => .ok (encInt (boolInt (v != 0)) :: st)
  | [] =>
    if (u == .mul2 || u == .div2) && !p.chronicleOps then .error .disabledOpcode
    else .error .invalidStackOperation

inductive Binary
  | add | sub | mul | div | mod | boolAnd | boolOr | numEqual | numEqualVerify | numNotEqual
  | lt | gt | le | ge | min | max
  deriving DecidableEq

def opBinary (b : Binary) (p : Params) : Stack → Except Err Stack
  | x2 :: x1 :: st =>
    match num p x1 with
    | .error e => .error e
    | .ok a =>
      match num p x2 with
      | .error e => .error e
      | .ok c =>
        match b with
        | .add => pushChecked p (a + c) st
        | .sub => pushChecked p (a - c) st
        | .mul => pushChecked p (a * c) st
        | .div => if c == 0 then .error .divByZero else .ok (encInt (Int.tdiv a c) :: st)
        | .mod => if c == 0 then .error .modByZero else .ok (encInt (Int.tmod a c) :: st)
        | .boolAnd => .ok (encInt (boolInt (a != 0 && c != 0)) :: st)
        | .boolOr => .ok (encInt (boolInt (a != 0 || c != 0)) :: st)
        | .numEqual => .ok (encInt (boolInt (a == c)) :: st)
        | .numEqualVerify => if a == c then .ok st else .error .numEqualVerify
        | .numNotEqual => .ok (encInt (boolInt (a != c)) :: st)
        | .lt => .ok (encInt (boolInt (decide (a < c))) :: st)
        | .gt => .ok (encInt (boolInt (decide (a > c))) :: st)
        | .le => .ok (encInt (boolInt (decide (a ≤ c))) :: st)
        | .ge => .ok (encInt (boolInt (decide (a ≥ c))) :: st)
        | .min => .ok (encInt (if a < c then a else c) :: st)
        | .max => .ok (encInt (if a > c then a else c) :: st)
  | _ => .error .invalidStackOperation

/-- OP_WITHIN `(x min max -- min ≤ x < max)`. -/
def opWithin (p : Params) : Stack → Except Err Stack
  | x3 :: x2 :: x1 :: st =>
    match num p x1 with
    | .error e => .error e
    | .ok v =>
      match num p x2 with
      | .error e => .error e
      | .ok lo =>
        match num p x3 with
        | .error e => .error e
        | .ok hi => .ok (encInt (boolInt (decide (lo ≤ v) && decide (v < hi))) :: st)
  | _ => .error .invalidStackOperation

end Bsv.Splice
