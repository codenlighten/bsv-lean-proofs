import BsvLeanProofs.ByteShiftLoop

/-!
Reads lines `<bytes, hex, or - for none> <count>` on standard input and prints
`<LShift result> <RShift result>` (hex) from the Lean transcriptions of the
source's `LShift` and `RShift` loops (`lshiftLoop`, `rshiftLoop`).
-/

open Bsv.Splice Bsv.ScriptNum

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else c.toNat - 87

def hexBytes : List Char → List Byte
  | a :: b :: r => BitVec.ofNat 8 (16 * hexVal a + hexVal b) :: hexBytes r
  | _ => []

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!

def showBytes (bs : List Byte) : String :=
  if bs.isEmpty then "-"
  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut line ← stdin.getLine
  while line != "" do
    match (line.trimAscii.toString.splitOn " ") with
    | [h, c] =>
      let x := if h == "-" then [] else hexBytes h.toList
      let n := c.toNat!
      stdout.putStrLn s!"{showBytes (lshiftLoop x n)} {showBytes (rshiftLoop x n)}"
    | _ => stdout.putStrLn "BAD"
    line ← stdin.getLine
