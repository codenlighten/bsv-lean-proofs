import BsvLeanProofs.MerkleMutation
import BsvLeanProofs.MerkleBranch0
import BsvLeanProofs.MerkleLiteral
import BsvLeanProofs.MerkleBranchAny

/-!
A test, not a proof. `computeLit` transcribes the `fn compute` of an
independent Rust node implementation (unpublished) with its array `inner`, its counter and its
branch logic, including the mutation flag. It is run on symbolic leaves
with a combining function that builds terms, so two results are equal here only
if they are the same expression in `H` and the leaves.
-/

open Bsv.Merkle

inductive T
  | leaf (n : Nat)
  | node (l r : T)
  deriving DecidableEq, Inhabited

def computeLit (leaves : Array T) (branchPos : Option Nat) : T × Array T × Bool := Id.run do
  let H := T.node
  let mut inner : Array T := Array.replicate 32 (T.leaf 0)
  let mut count := 0
  let mut matchLevel : Int := -1
  let mut branch : Array T := #[]
  let mut mutated := false
  for leaf in leaves do
    let mut hash := leaf
    let mut matched := branchPos == some count
    count := count + 1
    let mut level := 0
    while count &&& (1 <<< level) == 0 do
      if branchPos.isSome then
        if matched then
          branch := branch.push inner[level]!
        else if matchLevel == (level : Int) then
          branch := branch.push hash
          matched := true
      mutated := mutated || inner[level]! == hash
      hash := H inner[level]! hash
      level := level + 1
    inner := inner.set! level hash
    if matched then matchLevel := level
  let mut level := 0
  while count &&& (1 <<< level) == 0 do
    level := level + 1
  let mut hash := inner[level]!
  let mut matched := matchLevel == (level : Int)
  while count != (1 <<< level) do
    if branchPos.isSome && matched then branch := branch.push hash
    hash := H hash hash
    count := count + (1 <<< level)
    level := level + 1
    while count &&& (1 <<< level) == 0 do
      if branchPos.isSome then
        if matched then
          branch := branch.push inner[level]!
        else if matchLevel == (level : Int) then
          branch := branch.push hash
          matched := true
      hash := H inner[level]! hash
      level := level + 1
  return (hash, branch, mutated)

/-- The tree model's branch, with a self-pairing written as the node itself,
which is what `compute` pushes. -/
partial def branchSelfTest (l : List T) (i : Nat) : List T :=
  if l.length ≤ 1 then [] else
  (l[i ^^^ 1]?.getD l[i]!) :: branchSelfTest (level T.node l) (i / 2)

def main (args : List String) : IO UInt32 := do
  let maxN := (args.head? >>= String.toNat?).getD 200
  let mut bad := 0
  let mut checks := 0
  for n in [1:maxN + 1] do
    let l := (List.range n).map T.leaf
    let r := root T.node l
    let (rl, _, _) := computeLit l.toArray none
    checks := checks + 2
    if some rl != r then bad := bad + 1; IO.println s!"root mismatch (literal) n={n}"
    if rootCS T.node l != r then bad := bad + 1; IO.println s!"root mismatch (slots) n={n}"
    checks := checks + 1
    if rootLit T.node l != r then bad := bad + 1; IO.println s!"root mismatch (proved literal model) n={n}"
    let (_, b0, _) := computeLit l.toArray (some 0)
    checks := checks + 1
    if b0.toList != branchCS0 T.node l then bad := bad + 1; IO.println s!"branch-0 mismatch (slots) n={n}"
    for i in [0:n] do
      let (ri, bi, _) := computeLit l.toArray (some i)
      checks := checks + 3
      if some ri != r then bad := bad + 1; IO.println s!"root mismatch n={n} pos={i}"
      if bi.toList != branchSelfTest l i then bad := bad + 1; IO.println s!"branch mismatch n={n} pos={i}"
      checks := checks + 1
      if bi.toList != branchSelf T.node l i then bad := bad + 1; IO.println s!"branch mismatch (proved tree branch) n={n} pos={i}"
      checks := checks + 1
      if branchLit T.node i l != bi.toList then bad := bad + 1; IO.println s!"branch mismatch (Lean literal model) n={n} pos={i}"
      let spec := branch T.node l i
      let f := fold T.node l[i]! spec i
      if some f != r then bad := bad + 1; IO.println s!"fold mismatch n={n} pos={i}"
  IO.println s!"leaf counts 1..{maxN}: {checks} checks, {bad} mismatches"
  -- The mutation flag needs repeated leaves: every list over three symbols up to length 9.
  let mut lists : List (List T) := [[]]
  let mut mchecks := 0
  let mut flagged := 0
  for _ in [0:9] do
    lists := lists.flatMap (fun l => [T.leaf 0 :: l, T.leaf 1 :: l, T.leaf 2 :: l])
    for l in lists do
      let (rl, _, m) := computeLit l.toArray none
      mchecks := mchecks + 1
      if m then flagged := flagged + 1
      if m != mutatedTree T.node l || m != mutatedCS T.node l || some rl != root T.node l
          || m != mutatedLit T.node l || some rl != rootLit T.node l then
        bad := bad + 1
        IO.println s!"mutation mismatch on a list of length {l.length}"
  IO.println s!"mutation flag, lists over 3 symbols, lengths 1..9: {mchecks} lists, {flagged} flagged, {bad} mismatches in total"
  return if bad == 0 then 0 else 1
