import BsvLeanProofs.ScriptNum
import Lean.Data.Json

/-!
Runs the wide-index fixture cases (OP_SUBSTR / OP_LEFT / OP_RIGHT) through the
reader models of `BsvLeanProofs.ScriptNum`. Only the opcodes the fixtures use
are interpreted. This is a test harness: nothing in it is proved.

On the 1.2.3 verdicts: `SCRIPTNUM_OVERFLOW` is what the 1.2.3 source gives when
the reader returns nullopt (`CScriptNum` throws `scriptnum_overflow_error`,
which `interpreter.cpp` maps to `SCRIPT_ERR_SCRIPTNUM_OVERFLOW`). The text of
OP_SUBSTR, OP_LEFT and OP_RIGHT is the same at tags v1.2.2 and v1.2.3. No 1.2.3
binary was run here, so from this repository these verdicts are a prediction
from the source. An independent review reports (2026-10-07, not rerun
here) that the GoBDK libraries rebuilt from 1.2.3 give exactly these verdicts
on x86_64 and, under qemu, on aarch64, and accept the INT64_MIN encoding in the
reader as `deser123` does.
-/

open Bsv.ScriptNum

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def hexToBytes : List Char → List Byte
  | a :: b :: t => BitVec.ofNat 8 (16 * hexVal a + hexVal b) :: hexToBytes t
  | _ => []

/-- `CScriptNum::getint`: clamp to `int`. -/
def getint (v : I64) : Int := max (-2147483648) (min 2147483647 v.toInt)

def truthy (b : List Byte) : Bool :=
  match b.reverse with
  | [] => false
  | last :: rest => rest.any (· != 0) || (last != 0 && last != 0x80)

abbrev Reader := List Byte → Option I64

def reader122 : Reader := fun s => if s.isEmpty then some 0 else some (deser122 s)
def reader123 : Reader := deser123

/-- Script verdict names follow `script_error.h` without the prefix. -/
partial def run (rd : Reader) (minimal : Bool) : List Byte → List (List Byte) → String
  | [], top :: _ => if truthy top then "OK" else "EVAL_FALSE"
  | [], [] => "EVAL_FALSE"
  | op :: rest, st =>
    let n := op.toNat
    let num (b : List Byte) : Except String Int :=
      if minimal && !isMinimal b then .error "MINIMALDATA" else
      match rd b with
      | some v => .ok (getint v)
      | none => .error "SCRIPTNUM_OVERFLOW"
    if n == 0 then run rd minimal rest ([] :: st)
    else if n ≤ 0x4b then run rd minimal (rest.drop n) (rest.take n :: st)
    else if n == 0x4c then
      match rest with
      | l :: r => run rd minimal (r.drop l.toNat) (r.take l.toNat :: st)
      | [] => "BAD_OPCODE"
    else if n == 0x4f then run rd minimal rest ([0x81] :: st)
    else if 0x51 ≤ n && n ≤ 0x60 then run rd minimal rest ([BitVec.ofNat 8 (n - 0x50)] :: st)
    else if n == 0x75 then
      match st with
      | _ :: s => run rd minimal rest s
      | [] => "INVALID_STACK_OPERATION"
    else if n == 0x87 then
      match st with
      | a :: b :: s => run rd minimal rest ((if a == b then [1] else []) :: s)
      | _ => "INVALID_STACK_OPERATION"
    else if n == 0xb3 then
      match st with
      | l :: o :: data :: s =>
        match num l, num o with
        | .ok len, .ok offset =>
          let size : Int := data.length
          if offset < 0 || offset ≥ size || len < 0 || len > size - offset then "INVALID_NUMBER_RANGE"
          else run rd minimal rest ((data.drop offset.toNat).take len.toNat :: s)
        | .error e, _ => e
        | _, .error e => e
      | _ => "INVALID_STACK_OPERATION"
    else if n == 0xb4 || n == 0xb5 then
      match st with
      | l :: data :: s =>
        match num l with
        | .ok len =>
          let size : Int := data.length
          if len < 0 || len > size then "INVALID_NUMBER_RANGE"
          else if n == 0xb4 then run rd minimal rest (data.take len.toNat :: s)
          else run rd minimal rest (data.drop (size - len).toNat :: s)
        | .error e => e
      | _ => "INVALID_STACK_OPERATION"
    else "BAD_OPCODE"

/-- The 80 discriminating OP_RIGHT pairs: a bare array, each row asserting the
slice one reading predicts. The generic (scalar) reading must accept the
`expects-generic` rows and refuse the `expects-avx2` rows. -/
def runPairs (rows : Array Lean.Json) : IO UInt32 := do
  let mut okGeneric := 0
  let mut nGeneric := 0
  let mut refusedAvx2 := 0
  let mut nAvx2 := 0
  let mut over123 := 0
  for c in rows do
    let .ok id := c.getObjValAs? String "id" | throw (IO.userError "id")
    let .ok spk := c.getObjValAs? String "spk" | throw (IO.userError "spk")
    let script := hexToBytes spk.toList
    let v122 := run reader122 false script []
    if run reader123 false script [] == "SCRIPTNUM_OVERFLOW" then over123 := over123 + 1
    if id.endsWith "expects-generic" then
      nGeneric := nGeneric + 1
      if v122 == "OK" then okGeneric := okGeneric + 1 else IO.println s!"  MISMATCH {id}: model122 {v122}"
    else
      nAvx2 := nAvx2 + 1
      if v122 != "OK" then refusedAvx2 := refusedAvx2 + 1 else IO.println s!"  MISMATCH {id}: model122 OK"
  IO.println s!"rows: {rows.size}"
  IO.println s!"1.2.2 model accepts expects-generic rows: {okGeneric}/{nGeneric}"
  IO.println s!"1.2.2 model refuses expects-avx2 rows: {refusedAvx2}/{nAvx2}"
  IO.println s!"1.2.3 model gives script-number overflow (a prediction): {over123}/{rows.size}"
  return if okGeneric == nGeneric && refusedAvx2 == nAvx2 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let path := args.head!
  let txt ← IO.FS.readFile path
  let .ok j := Lean.Json.parse txt | throw (IO.userError "bad json")
  if let .arr rows := j then return ← runPairs rows
  let .ok cases := j.getObjValAs? (Array Lean.Json) "cases" | throw (IO.userError "no cases")
  let mut agree122 := 0
  let mut bad : Array String := #[]
  let mut tally123 : Array (String × String × Nat) := #[]
  for c in cases do
    let .ok id := c.getObjValAs? String "id" | throw (IO.userError "id")
    let .ok spk := c.getObjValAs? String "scriptPubKey" | throw (IO.userError "spk")
    let .ok flags := c.getObjValAs? Nat "flags" | throw (IO.userError "flags")
    let .ok expected := c.getObjValAs? String "expected" | throw (IO.userError "expected")
    let script := hexToBytes spk.toList
    let minimal := flags &&& 0x40 != 0
    let v122 := run reader122 minimal script []
    let v123 := run reader123 minimal script []
    if v122 == expected then agree122 := agree122 + 1 else bad := bad.push s!"{id}: expected {expected}, model122 {v122}"
    match tally123.findIdx? (fun (e, v, _) => e == expected && v == v123) with
    | some i => tally123 := tally123.modify i (fun (e, v, k) => (e, v, k + 1))
    | none => tally123 := tally123.push (expected, v123, 1)
  IO.println s!"cases: {cases.size}"
  IO.println s!"1.2.2 model (x86 scalar fold) agrees with expected: {agree122}/{cases.size}"
  for b in bad do IO.println s!"  MISMATCH {b}"
  IO.println "1.2.3 model verdicts, by the fixture's 1.2.2 expectation (a prediction; no 1.2.3 referee was run):"
  for (e, v, k) in tally123 do IO.println s!"  1.2.2 expected {e} -> 1.2.3 model {v}: {k}"
  return if bad.isEmpty then 0 else 1
