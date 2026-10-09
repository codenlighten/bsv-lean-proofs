import BsvLeanProofs.ScriptNum
import BsvLeanProofs.RoundTrip
import BsvLeanProofs.SighashType

/-!
Differential-test harness, not a proof. Prints what the Lean models return so
that the output can be compared, line for line, with a driver compiled from the
unmodified C++ header.

  readercheck deser123   -- stdin: hex byte strings; stdout: value or "none"
  readercheck deser122   -- stdin: non-empty hex byte strings; stdout: value
  readercheck ser        -- stdin: signed decimal int64 values; stdout: hex
  readercheck sighash170 | sighashMaster
                         -- no input; one line per flag setting and byte, in the
                         -- format of the Go dump tests in difftest/
-/

open Bsv.ScriptNum

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def hexToBytes : List Char → List Byte
  | a :: b :: t => BitVec.ofNat 8 (16 * hexVal a + hexVal b) :: hexToBytes t
  | _ => []

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def bytesToHex (bs : List Byte) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def hex2 (n : Nat) : String := String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

def verdictName : Bsv.SighashType.Verdict → String
  | .accept => "accept"
  | .invalidSigHashType => "ErrInvalidSigHashType"
  | .illegalForkID => "ErrIllegalForkID"
  | .illegalChronicle => "ErrIllegalChronicle"
  | .mustUseForkID => "ErrMustUseForkID"

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (f : String → String) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  out.putStrLn (f (String.ofList (line.toList.filter (fun c => c != '\n' && c != '\r'))))
  loop h out f

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  match args with
  | ["deser123"] =>
    loop stdin stdout fun s =>
      match deser123 (hexToBytes s.toList) with
      | some v => toString v.toInt
      | none => "none"
  | ["deser122"] =>
    loop stdin stdout fun s => toString (deser122 (hexToBytes s.toList)).toInt
  | ["ser"] =>
    loop stdin stdout fun s => bytesToHex (ser (BitVec.ofInt 64 s.toInt!))
  | ["sighash170"] =>
    for strict in [false, true] do
      for bip143 in [false, true] do
        for forkid in [false, true] do
          for after in [false, true] do
            for b in [0:256] do
              let v := Bsv.SighashType.check170 strict bip143 forkid after (BitVec.ofNat 8 b)
              stdout.putStrLn s!"{strict} {bip143} {forkid} {after} {hex2 b} {verdictName v}"
  | ["sighashMaster"] =>
    for strict in [false, true] do
      for bip143 in [false, true] do
        for forkid in [false, true] do
          for chron in [false, true] do
            for b in [0:256] do
              let v := Bsv.SighashType.checkMaster strict bip143 forkid chron (BitVec.ofNat 8 b)
              stdout.putStrLn s!"{strict} {bip143} {forkid} {chron} {hex2 b} {verdictName v}"
  | ["sighashNode"] =>
    for strict in [false, true] do
      for forkid in [false, true] do
        for chron in [false, true] do
          for b in [0:256] do
            let v := Bsv.SighashType.nodeVerifyScript strict forkid chron (BitVec.ofNat 8 b)
            stdout.putStrLn s!"{strict} {forkid} {chron} {hex2 b} {verdictName v}"
  | _ => IO.eprintln "usage: readercheck deser123|deser122|ser|sighash170|sighashMaster|sighashNode"; return 2
  return 0
