import BsvLeanProofs.MerkleVerify

/-!
Differential-test harness, not a proof. For each input line `pos|s1 s2 ... sn`
(a requested position and a list of leaf symbols, repeats allowed) it prints
what the proved literal model returns, as expressions over the symbols:

  <root>|<mutated>|<branch entry>;<branch entry>;...

where an expression is `L<k>` for the leaf with symbol `k` or `(N <e> <e>)` for
a combined pair. `difftest/merkle_compare.py` evaluates these with double
SHA-256 and compares with the reference node's ComputeMerkleRoot /
ComputeMerkleBranch.
-/

open Bsv.Merkle

inductive T
  | leaf (n : Nat)
  | node (l r : T)
  deriving DecidableEq, Inhabited

def T.show : T → String
  | .leaf n => s!"L{n}"
  | .node l r => s!"(N {l.show} {r.show})"

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (f : String → String) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  out.putStrLn (f (String.ofList (line.toList.filter (fun c => c != '\n' && c != '\r'))))
  loop h out f

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout fun s =>
    match s.splitOn "|" with
    | [p, syms] =>
      let pos := p.toNat!
      let l := (syms.splitOn " ").filter (· ≠ "") |>.map (fun x => T.leaf x.toNat!)
      let r := match rootLit T.node l with
        | some t => t.show
        | none => "-"
      let m := if mutatedLit T.node l then "1" else "0"
      let b := ";".intercalate ((branchLit T.node pos l).map T.show)
      s!"{r}|{m}|{b}"
    | _ => "?"
  return 0
