import BsvLeanProofs.ScriptNum

/-!
# Reference semantics, slice 1: the splice and conversion opcodes

OP_CAT, OP_SPLIT, OP_NUM2BIN, OP_BIN2NUM, OP_SIZE and the Chronicle opcodes
OP_SUBSTR, OP_LEFT, OP_RIGHT, as TOTAL functions from a stack to a new stack or
a named script error. Written from bitcoin-sv v1.2.3: `src/script/interpreter.cpp`,
`script_num.cpp` (the `CScriptNum` constructor and `getint`),
`int_serialization.h` (`MinimallyEncode`, `IsMinimallyEncoded`) and
`limitedstack.cpp` (`padRight`).

What is modelled: what each opcode does to the stack, and which error it
returns, as a function of the three things the source reads: `requireMinimal`,
`MaxScriptNumLength` and whether the output being spent is after Genesis (which
selects the big-integer or the narrow number reader, and the 520-byte limit).
What is not modelled: stack-memory accounting, the limits on script size,
opcode count and stack depth, and the big-integer reader's internals:
`bint::deserialize` is taken to return the integer the bytes denote.
A stack is a list with the top element first.
-/

namespace Bsv.Splice

open Bsv.ScriptNum

abbrev Elem := List Byte
abbrev Stack := List Elem

/-- The script errors these opcodes can return (`script_error.h`, without the
`SCRIPT_ERR_` prefix). -/
inductive Err
  | invalidStackOperation
  | scriptNumOverflow
  | scriptNumMinEncode
  | invalidNumberRange
  | invalidSplitRange
  | pushSize
  | impossibleEncoding
  | discourageUpgradableNops
  | divByZero
  | modByZero
  | numEqualVerify
  | disabledOpcode
  deriving DecidableEq, Repr

/-- What the opcodes read from the flags and the policy.
* `requireMinimal`: MINIMALDATA is enforced for numbers.
* `maxNumLen`: `MaxScriptNumLength`. Under consensus rules it is 4 for an
  output created before Genesis, 750,000 after Genesis and 32,000,000 after
  Chronicle.
* `afterGenesis`: the output being spent was created after Genesis.
* `chronicleOps`: the output was created after Chronicle, so OP_SUBSTR, OP_LEFT
  and OP_RIGHT are opcodes and not reserved no-ops.
* `discourageNops`: DISCOURAGE_UPGRADABLE_NOPS is set. -/
structure Params where
  requireMinimal : Bool
  maxNumLen : Nat
  afterGenesis : Bool
  chronicleOps : Bool := true
  discourageNops : Bool := false

/-- `MAX_SCRIPT_ELEMENT_SIZE_BEFORE_GENESIS`. -/
def maxElemBeforeGenesis : Nat := 520

def int32Max : Int := 2147483647
def int32Min : Int := -2147483648

/-- `bsv::IsMinimallyEncoded(span, nMaxNumSize)`. -/
def isMinimalMax (s : Elem) (maxLen : Nat) : Bool := decide (s.length ≤ maxLen) && isMinimal s

/-! ## `bsv::MinimallyEncode`

The source works on the vector in place from its last byte downward. The model
works on the reversed list, so its head is the source's last byte. -/

/-- The loop `for (i = size - 1; i > 0; i--)`: skip zero bytes; at the first
non-zero byte either append the sign byte (if that byte's top bit is set) or
merge the sign into it. `rb` is the body (all but the last byte), reversed. -/
def trim (last : Byte) : List Byte → List Byte
  | [] => []
  | b :: bs =>
    if b == 0#8 then trim last bs
    else if (b &&& 0x80#8) != 0#8 then last :: b :: bs
    else (b ||| last) :: bs

/-- `MinimallyEncode` on the reversed vector. -/
def minEncRev : List Byte → List Byte
  | [] => []
  | last :: rest =>
    if (last &&& 0x7f#8) != 0#8 then last :: rest
    else match rest with
      | [] => []
      | second :: _ =>
        if (second &&& 0x80#8) != 0#8 then last :: rest
        else trim last rest

/-- `bsv::MinimallyEncode(data)`: the vector afterwards. -/
def minEnc (s : Elem) : Elem := (minEncRev s.reverse).reverse

/-! ## Numbers -/

/-- The `CScriptNum` constructor from bytes, as the integer it holds.
`bigInt = false` is the narrow reader (`deser123`). -/
def scriptNum (requireMinimal : Bool) (maxLen : Nat) (bigInt : Bool) (s : Elem) : Except Err Int :=
  if s.length > maxLen then .error .scriptNumOverflow
  else if requireMinimal && !isMinimalMax s maxLen then .error .scriptNumMinEncode
  else if s.isEmpty then .ok 0
  else if bigInt then .ok (denote s)
  else match deser123 s with
    | some v => .ok v.toInt
    | none => .error .scriptNumOverflow

/-- `CScriptNum::getint`: clamp to `int`. -/
def getint (n : Int) : Int := max int32Min (min int32Max n)

/-- The minimal encoding of a natural number (`bint::serialize` of a
non-negative value): little-endian bytes, plus a zero byte if the top bit of
the last one is set. -/
def encNatLoop : Nat → Nat → List Byte
  | 0, _ => []
  | fuel + 1, n =>
    if n == 0 then []
    else if n < 128 then [BitVec.ofNat 8 n]
    else if n < 256 then [BitVec.ofNat 8 n, 0#8]
    else BitVec.ofNat 8 (n % 256) :: encNatLoop fuel (n / 256)

def encNat (n : Nat) : Elem := encNatLoop (n + 1) n

/-! ## The opcodes -/

/-- OP_CAT `(x1 x2 -- x1 ++ x2)`. -/
def opCat (p : Params) : Stack → Except Err Stack
  | x2 :: x1 :: st =>
    if !p.afterGenesis && decide (x1.length + x2.length > maxElemBeforeGenesis) then .error .pushSize
    else .ok ((x1 ++ x2) :: st)
  | _ => .error .invalidStackOperation

/-- OP_SPLIT `(data position -- left right)`. -/
def opSplit (p : Params) : Stack → Except Err Stack
  | top :: data :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 || n > int32Max || n > (data.length : Int) then .error .invalidSplitRange
      else .ok (data.drop n.toNat :: data.take n.toNat :: st)
  | _ => .error .invalidStackOperation

/-- OP_NUM2BIN `(number size -- number padded to size bytes)`. -/
def opNum2Bin (p : Params) : Stack → Except Err Stack
  | top :: rawnum :: st =>
    match scriptNum p.requireMinimal p.maxNumLen p.afterGenesis top with
    | .error e => .error e
    | .ok n =>
      if n < 0 || n > int32Max then .error .pushSize
      else
        let size := n.toNat
        if !p.afterGenesis && decide (size > maxElemBeforeGenesis) then .error .pushSize
        else
          let r := minEnc rawnum
          if r.length > size then .error .impossibleEncoding
          else if r.length == size then .ok (r :: st)
          else
            -- move the sign bit to the new last byte
            let signbit : Byte := match r.getLast? with
              | some l => l &&& 0x80#8
              | none => 0#8
            let cleared : Elem := match r.reverse with
              | [] => []
              | l :: rb => ((l &&& 0x7f#8) :: rb).reverse
            .ok ((cleared ++ List.replicate (size - r.length - 1) 0#8 ++ [signbit]) :: st)
  | _ => .error .invalidStackOperation

/-- OP_BIN2NUM `(bytes -- minimally encoded number)`. -/
def opBin2Num (p : Params) : Stack → Except Err Stack
  | x :: st =>
    let r := minEnc x
    if !isMinimalMax r p.maxNumLen then .error .invalidNumberRange
    else .ok (r :: st)
  | _ => .error .invalidStackOperation

/-- OP_SIZE `(x -- x size)`. -/
def opSize (p : Params) : Stack → Except Err Stack
  | x :: st =>
    let e := encNat x.length
    if e.length > p.maxNumLen then .error .scriptNumOverflow
    else .ok (e :: x :: st)
  | _ => .error .invalidStackOperation

/-- The length or offset operand of the Chronicle opcodes: always the narrow
reader, then `getint`. -/
def chronicleInt (p : Params) (s : Elem) : Except Err Int :=
  (scriptNum p.requireMinimal p.maxNumLen false s).map getint

/-- OP_SUBSTR `(data offset length -- slice)`. -/
def opSubstr (p : Params) : Stack → Except Err Stack
  | l :: o :: data :: st =>
    match chronicleInt p l with
    | .error e => .error e
    | .ok len =>
      match chronicleInt p o with
      | .error e => .error e
      | .ok offset =>
        let size : Int := data.length
        if offset < 0 || offset ≥ size || len < 0 || len > size - offset then
          .error .invalidNumberRange
        else .ok ((data.drop offset.toNat).take len.toNat :: st)
  | _ => .error .invalidStackOperation

/-- OP_LEFT `(data length -- first length bytes)`. -/
def opLeft (p : Params) : Stack → Except Err Stack
  | l :: data :: st =>
    match chronicleInt p l with
    | .error e => .error e
    | .ok len =>
      if len < 0 || len > (data.length : Int) then .error .invalidNumberRange
      else .ok (data.take len.toNat :: st)
  | _ => .error .invalidStackOperation

/-- OP_RIGHT `(data length -- last length bytes)`. -/
def opRight (p : Params) : Stack → Except Err Stack
  | l :: data :: st =>
    match chronicleInt p l with
    | .error e => .error e
    | .ok len =>
      if len < 0 || len > (data.length : Int) then .error .invalidNumberRange
      else .ok (data.drop (data.length - len.toNat) :: st)
  | _ => .error .invalidStackOperation

/-- The activation gate of the three Chronicle opcodes: for an output created
before Chronicle they are reserved no-ops, refused only when
DISCOURAGE_UPGRADABLE_NOPS is set. -/
def chronicleGate (p : Params) (op : Params → Stack → Except Err Stack) (st : Stack) :
    Except Err Stack :=
  if p.chronicleOps then op p st
  else if p.discourageNops then .error .discourageUpgradableNops
  else .ok st

/-! ## The same three opcodes as v1.2.2 runs them (x86 scalar build)

Only the number reader differs: `deser122`, which never fails. Used to compare
the model with a compiled 1.2.2 node on every row, including the rows on which
the two versions disagree. -/

def chronicleInt122 (p : Params) (s : Elem) : Except Err Int :=
  if s.length > p.maxNumLen then .error .scriptNumOverflow
  else if p.requireMinimal && !isMinimalMax s p.maxNumLen then .error .scriptNumMinEncode
  else if s.isEmpty then .ok 0
  else .ok (getint (deser122 s).toInt)

def opSubstr122 (p : Params) : Stack → Except Err Stack
  | l :: o :: data :: st =>
    match chronicleInt122 p l with
    | .error e => .error e
    | .ok len =>
      match chronicleInt122 p o with
      | .error e => .error e
      | .ok offset =>
        let size : Int := data.length
        if offset < 0 || offset ≥ size || len < 0 || len > size - offset then
          .error .invalidNumberRange
        else .ok ((data.drop offset.toNat).take len.toNat :: st)
  | _ => .error .invalidStackOperation

def opLeft122 (p : Params) : Stack → Except Err Stack
  | l :: data :: st =>
    match chronicleInt122 p l with
    | .error e => .error e
    | .ok len =>
      if len < 0 || len > (data.length : Int) then .error .invalidNumberRange
      else .ok (data.take len.toNat :: st)
  | _ => .error .invalidStackOperation

def opRight122 (p : Params) : Stack → Except Err Stack
  | l :: data :: st =>
    match chronicleInt122 p l with
    | .error e => .error e
    | .ok len =>
      if len < 0 || len > (data.length : Int) then .error .invalidNumberRange
      else .ok (data.drop (data.length - len.toNat) :: st)
  | _ => .error .invalidStackOperation

end Bsv.Splice
