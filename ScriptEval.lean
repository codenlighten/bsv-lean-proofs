import BsvLeanProofs.Interp

/-!
Reads lines `<tx version> <flag word, hex> <script, hex>` on standard input and
prints the model's verdict for each (`Bsv.Interp.verify`), in the node's error
names, or `OUT_OF_MODEL`.
-/

open Bsv.Splice Bsv.Interp

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87
  else c.toNat - 55

def hexNat (s : String) : Nat := s.toList.foldl (fun a c => 16 * a + hexVal c) 0

def hexBytes : List Char → List Bsv.ScriptNum.Byte
  | a :: b :: r => BitVec.ofNat 8 (16 * hexVal a + hexVal b) :: hexBytes r
  | _ => []

def opErr : Err → String
  | .invalidStackOperation => "INVALID_STACK_OPERATION"
  | .scriptNumOverflow => "SCRIPTNUM_OVERFLOW"
  | .scriptNumMinEncode => "SCRIPTNUM_MINENCODE"
  | .invalidNumberRange => "INVALID_NUMBER_RANGE"
  | .invalidSplitRange => "INVALID_SPLIT_RANGE"
  | .pushSize => "PUSH_SIZE"
  | .impossibleEncoding => "IMPOSSIBLE_ENCODING"
  | .discourageUpgradableNops => "DISCOURAGE_UPGRADABLE_NOPS"
  | .divByZero => "DIV_BY_ZERO"
  | .modByZero => "MOD_BY_ZERO"
  | .numEqualVerify => "NUMEQUALVERIFY"
  | .disabledOpcode => "DISABLED_OPCODE"

def name : Option IErr → String
  | none => "OK"
  | some (.op e) => opErr e
  | some .bigInt => "BIG_INT"
  | some .badOpcode => "BAD_OPCODE"
  | some .unbalancedConditional => "UNBALANCED_CONDITIONAL"
  | some .verify => "VERIFY"
  | some .equalVerify => "EQUALVERIFY"
  | some .opReturn => "OP_RETURN"
  | some .opCount => "OP_COUNT"
  | some .scriptSize => "SCRIPT_SIZE"
  | some .stackSize => "STACK_SIZE"
  | some .minimalData => "MINIMALDATA"
  | some .minimalIf => "MINIMALIF"
  | some .invalidAltstackOperation => "INVALID_ALTSTACK_OPERATION"
  | some .invalidOperandSize => "INVALID_OPERAND_SIZE"
  | some .evalFalse => "EVAL_FALSE"
  | some .cleanStack => "CLEANSTACK"
  | some .invalidFlags => "INVALID_FLAGS"
  | some .outOfModel => "OUT_OF_MODEL"

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ") with
  | [v, f, s] =>
    out.putStrLn (name (verify (cfgOf v.toNat! (hexNat f)) (hexBytes s.toList)))
  | [v, f] => out.putStrLn (name (verify (cfgOf v.toNat! (hexNat f)) []))
  | _ => out.putStrLn "BAD_LINE"
  loop h out

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
