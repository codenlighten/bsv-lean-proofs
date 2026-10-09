import BsvLeanProofs.Splice
import BsvLeanProofs.RoundTrip
import BsvLeanProofs.Arith

/-!
Generates conformance vectors for the splice and conversion opcodes FROM THE
MODEL in `BsvLeanProofs.Splice`: every expected verdict is what the Lean
definitions return, not an observation of some implementation.

Output: one JSON document `{"source": …, "cases": [ … ]}` in the shape of
a common script-fixture format (`id`, `txHex`, `amount`, `scriptPubKey`, `flags`,
`expected`), with extra fields: `opcode`, `covers`, `expected_1_2_2` (what the
1.2.2 model returns, for comparison with a 1.2.2 node), `utxo` and `spend`
(the two era markers).

Three eras of the output being spent are covered, each under the block flag
word and the stricter relay word, always spent with Chronicle active:
before Genesis, after Genesis, and after Chronicle. A row that the model
accepts ends by comparing the WHOLE resulting stack with the model's
(`OP_EQUALVERIFY … OP_1`), so a node accepting it confirms the result.
-/

open Bsv.ScriptNum Bsv.Splice

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
def toHex (bs : List Byte) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])
def B (l : List Nat) : Elem := l.map (BitVec.ofNat 8)

/-- A minimal push of `b`, so that MINIMALDATA judges the opcode and not the push. -/
def push (b : Elem) : List Byte :=
  let n := b.length
  if n == 0 then B [0x00]
  else if n == 1 && 1 ≤ b[0]!.toNat && b[0]!.toNat ≤ 16 then B [0x50 + b[0]!.toNat]
  else if b == B [0x81] then B [0x4f]
  else if n < 0x4c then B [n] ++ b
  else if n ≤ 0xff then B [0x4c, n] ++ b
  else if n ≤ 0xffff then B [0x4d, n % 256, n / 256] ++ b
  else B [0x4e, n % 256, n / 256 % 256, n / 65536 % 256, n / 16777216] ++ b

def errName : Err → String
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

def OP_DROP := 0x75
def OP_1 := 0x51
def OP_EQUALVERIFY := 0x88

def txHex : String :=
  "0100000001aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000ffffffff01905f0100000000001976a914925d4028880bd0c9d68fbc7fc7dfee976698629c88ac00000000"

/-- The era of the output being spent. -/
inductive Era | preGenesis | postGenesis | postChronicle
  deriving DecidableEq

def Era.name : Era → String
  | .preGenesis => "before-genesis"
  | .postGenesis => "after-genesis"
  | .postChronicle => "after-chronicle"

def Era.tag : Era → String
  | .preGenesis => "pg"
  | .postGenesis => "g"
  | .postChronicle => "c"

/-- The consensus flag word used for blocks and the stricter relay word, with
the two "output created after …" bits (19 and 21) set as the era requires. -/
def flagsOf (era : Era) (relay : Bool) : Nat :=
  let base := if relay then 0x3d47ff else 0x3d462f
  match era with
  | .postChronicle => base
  | .postGenesis => base - 0x200000
  | .preGenesis => base - 0x200000 - 0x80000

def paramsOf (era : Era) (relay : Bool) : Params :=
  { requireMinimal := relay,
    maxNumLen := match era with | .preGenesis => 4 | .postGenesis => 750000 | .postChronicle => 32000000,
    afterGenesis := era != .preGenesis,
    chronicleOps := era == .postChronicle,
    discourageNops := relay }

/-- The script for a verdict: on acceptance compare the whole resulting stack
(top first) with the model's; on an error the tail is never reached. -/
def tailOf (res : Except Err Stack) : List Byte :=
  match res with
  | .ok st => st.flatMap (fun e => push e ++ B [OP_EQUALVERIFY]) ++ B [OP_1]
  | .error _ => B [OP_DROP, OP_1]

def verdict (res : Except Err Stack) : String :=
  match res with
  | .ok _ => "OK"
  | .error e => errName e

structure Row where
  id : String
  era : Era
  opcode : String
  covers : String
  spk : List Byte
  flags : Nat
  expected : String
  expected122 : String

/-- The theorems (in `Bsv.Splice` unless prefixed) that describe what an
accepted row of each opcode must return. -/
def theoremsFor : String → String
  | "OP_CAT" => "opSplit_then_opCat"
  | "OP_SPLIT" => "opSplit_ok, opSplit_then_opCat"
  | "OP_NUM2BIN" => "opNum2Bin_ok, denote_minEnc, opBin2Num_opNum2Bin"
  | "OP_BIN2NUM" => "opBin2Num_ok, opBin2Num_error, isMinimal_minEnc, minimal_unique"
  | "OP_SIZE" => "opSize_ok, denote_encNat"
  | "OP_LEFT" => "opLeft_ok, left_append_right, chronicleInt_wide, ScriptNum.deser123_spec"
  | "OP_RIGHT" => "opRight_ok, left_append_right, chronicleInt_wide, ScriptNum.deser123_spec"
  | "OP_SUBSTR" => "opSubstr_ok, chronicleInt_wide, ScriptNum.deser123_spec"
  | "OP_LSHIFTNUM" => "opLShiftNum_ok"
  | "OP_RSHIFTNUM" => "opRShiftNum_ok"
  | "OP_LSHIFT" => "opLShift_length"
  | "OP_RSHIFT" => "opRShift_length"
  | _ => ""

/-- The node's names for the bits of a flag word (`script_flags.h`, without the
`SCRIPT_VERIFY_` / `SCRIPT_ENABLE_` / `SCRIPT_` prefix). -/
def flagBits : List (Nat × String) :=
  [ (0, "P2SH"), (1, "STRICTENC"), (2, "DERSIG"), (3, "LOW_S"), (4, "NULLDUMMY"),
    (5, "SIGPUSHONLY"), (6, "MINIMALDATA"), (7, "DISCOURAGE_UPGRADABLE_NOPS"), (8, "CLEANSTACK"),
    (9, "CHECKLOCKTIMEVERIFY"), (10, "CHECKSEQUENCEVERIFY"), (13, "MINIMALIF"), (14, "NULLFAIL"),
    (15, "COMPRESSED_PUBKEYTYPE"), (16, "SIGHASH_FORKID"), (18, "GENESIS"),
    (19, "UTXO_AFTER_GENESIS"), (20, "CHRONICLE"), (21, "UTXO_AFTER_CHRONICLE") ]

def flagNames (w : Nat) : String :=
  "[" ++ ", ".intercalate ((flagBits.filter (fun (b, _) => w.testBit b)).map
    (fun (_, n) => "\"" ++ n ++ "\"")) ++ "]"

def Row.json (r : Row) : String :=
  "{\"id\": \"" ++ r.id ++ "\", \"opcode\": \"" ++ r.opcode ++ "\", \"covers\": \"" ++ r.covers ++
  "\", \"theorems\": \"" ++ theoremsFor r.opcode ++
  "\", \"utxo\": \"" ++ r.era.name ++ "\", \"spend\": \"chronicle\", \"txHex\": \"" ++ txHex ++
  "\", \"amount\": 100000, \"scriptPubKey\": \"" ++ toHex r.spk ++ "\", \"flags\": " ++ toString r.flags ++
  ", \"flagset\": " ++ flagNames r.flags ++
  ", \"expected\": \"" ++ r.expected ++ "\", \"expected_1_2_2\": \"" ++ r.expected122 ++ "\"}"

/-- One case in every era under both flag words. `args` are pushed in order
(the last is the top of the stack). `op122` is the 1.2.2 behaviour when it
differs. -/
def mkRows (opname : String) (opbyte : Nat)
    (op : Params → Stack → Except Err Stack) (op122 : Params → Stack → Except Err Stack)
    (idx : Nat) (covers : String) (args : List Elem) : List Row :=
  [Era.postChronicle, Era.postGenesis, Era.preGenesis].flatMap fun era =>
  [false, true].map fun relay =>
    let p := paramsOf era relay
    let st := args.reverse
    let res := op p st
    let res122 := op122 p st
    -- the script asserts the 1.2.3 result; a 1.2.2 node that computes another
    -- result fails the comparison
    let exp122 := match res, res122 with
      | .ok a, .ok b => if a == b then "OK" else "EQUALVERIFY"
      | .ok _, .error e => errName e
      | .error _, .ok _ => "OK"
      | .error _, .error e => errName e
    { id := s!"{opname}-{idx}-{era.tag}-{if relay then "relay" else "block"}", era := era,
      opcode := opname, covers := covers,
      spk := args.flatMap push ++ B [opbyte] ++ tailOf res,
      flags := flagsOf era relay,
      expected := verdict res, expected122 := exp122 }

def i64 (n : Int) : Elem := ser (BitVec.ofInt 64 n)

/-- Number operands, each with what it is meant to cover. -/
def operands : List (String × Elem) :=
  [ ("zero, empty", []), ("one", i64 1), ("two", i64 2), ("three", i64 3), ("five", i64 5),
    ("sixteen", i64 16), ("seventeen", i64 17), ("59", i64 59), ("60", i64 60), ("61", i64 61),
    ("127", i64 127), ("128, needs a zero byte", i64 128), ("255", i64 255), ("256", i64 256),
    ("minus one", i64 (-1)), ("minus five", i64 (-5)), ("minus 128", i64 (-128)),
    ("INT32_MAX", i64 2147483647), ("INT32_MAX + 1", i64 2147483648), ("2^32", i64 4294967296),
    ("INT64_MAX", i64 9223372036854775807),
    ("INT64_MIN, the only accepted minimal nine-byte operand", i64 (-9223372036854775808)),
    ("non-minimal one: 01 00", B [1, 0]), ("non-minimal zero: 00", B [0]),
    ("negative zero: 80", B [0x80]), ("non-minimal minus five: 05 80", B [5, 0x80]),
    ("nine bytes, padded one", B [1, 0, 0, 0, 0, 0, 0, 0, 0]),
    ("nine bytes, 05 00x7 80: -5 in 1.2.3, 5 in 1.2.2", B [5, 0, 0, 0, 0, 0, 0, 0, 0x80]),
    ("nine bytes, magnitude in the ninth: 05 00x7 01", B [5, 0, 0, 0, 0, 0, 0, 0, 1]),
    ("nine bytes, 2^63: out of int64", B [0, 0, 0, 0, 0, 0, 0, 0x80, 0]),
    ("nine bytes, minimal, 2^64 - 1", B [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0]),
    ("ten bytes, padded one", B [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    ("ten bytes, minimal", B [1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    ("seventeen bytes, small low word", B [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    ("seventeen bytes, wraps onto bit 6", B [3, 0, 0, 0, 0, 0, 0, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 1]),
    ("thirty-three bytes", B ((List.range 32).map (fun i => if i % 8 == 0 then 2 else 0) ++ [1])) ]

def data60 : Elem := B ((List.range 60).map (· + 1))
def data5 : Elem := B [1, 2, 3, 4, 5]
def big260 : Elem := B ((List.range 260).map (fun i => i % 251 + 1))

/-- Elements for the conversion opcodes. -/
def elems : List (String × Elem) :=
  operands ++
  [ ("zeros 00 00 00", B [0, 0, 0]), ("00 80, negative zero padded", B [0, 0x80]),
    ("01 00 80, minus one padded", B [1, 0, 0x80]), ("ff 00", B [0xff, 0]), ("ff 80", B [0xff, 0x80]),
    ("ff 00 00", B [0xff, 0, 0]), ("7f", B [0x7f]), ("80 00", B [0x80, 0]),
    ("data of five bytes", data5), ("data of sixty bytes", data60) ]

def enumFrom' {α} (l : List α) : List (Nat × α) := (List.range l.length).zip l

def rows : List Row := Id.run do
  let same (f : Params → Stack → Except Err Stack) := f
  let mut out : List Row := []
  -- OP_CAT
  for (i, (c1, a), (c2, b)) in enumFrom' [(("empty", ([] : Elem)), ("empty", ([] : Elem))),
      (("empty", []), ("five bytes", data5)), (("five bytes", data5), ("empty", [])),
      (("five bytes", data5), ("sixty bytes", data60)), (("sixty bytes", data60), ("sixty bytes", data60)),
      (("260 bytes", big260), ("260 bytes", big260)), (("261 bytes", big260 ++ B [9]), ("260 bytes", big260)),
      (("520 bytes", big260 ++ big260), ("empty", [])), (("520 bytes", big260 ++ big260), ("one byte", B [7]))] do
    out := out ++ mkRows "OP_CAT" 0x7e opCat (same opCat) i s!"{c1} then {c2}" [a, b]
  -- OP_SPLIT
  let mut k := 0
  for (cd, d) in [("empty data", ([] : Elem)), ("five bytes", data5), ("sixty bytes", data60)] do
    for (co, o) in operands do
      out := out ++ mkRows "OP_SPLIT" 0x7f opSplit (same opSplit) k s!"{cd}; position {co}" [d, o]
      k := k + 1
  -- OP_NUM2BIN
  k := 0
  for (ce, e) in elems do
    for (cs, s) in [("size 0", ([] : Elem)), ("size 1", i64 1), ("size 2", i64 2), ("size 3", i64 3),
        ("size 4", i64 4), ("size 8", i64 8), ("size 9", i64 9), ("size 10", i64 10), ("size 33", i64 33),
        ("size 600, above the pre-Genesis limit", i64 600), ("size -1", i64 (-1)),
        ("size INT32_MAX + 1", i64 2147483648), ("size 2^32", i64 4294967296),
        ("size given non-minimally: 02 00", B [2, 0]), ("size as nine bytes", B [9, 0, 0, 0, 0, 0, 0, 0, 0])] do
      out := out ++ mkRows "OP_NUM2BIN" 0x80 opNum2Bin (same opNum2Bin) k s!"{ce}; {cs}" [e, s]
      k := k + 1
  -- OP_BIN2NUM, OP_SIZE
  for (i, (ce, e)) in enumFrom' elems do
    out := out ++ mkRows "OP_BIN2NUM" 0x81 opBin2Num (same opBin2Num) i ce [e]
    out := out ++ mkRows "OP_SIZE" 0x82 opSize (same opSize) i ce [e]
  -- OP_LEFT, OP_RIGHT
  for (i, (co, o)) in enumFrom' operands do
    out := out ++ mkRows "OP_LEFT" 0xb4 (fun p => chronicleGate p opLeft) (fun p => chronicleGate p opLeft122) i s!"sixty bytes; length {co}" [data60, o]
    out := out ++ mkRows "OP_RIGHT" 0xb5 (fun p => chronicleGate p opRight) (fun p => chronicleGate p opRight122) i s!"sixty bytes; length {co}" [data60, o]
  -- OP_SUBSTR: wide offset with a narrow length, and the reverse
  k := 0
  for (co, o) in operands do
    out := out ++ mkRows "OP_SUBSTR" 0xb3 (fun p => chronicleGate p opSubstr) (fun p => chronicleGate p opSubstr122) k s!"offset {co}; length one" [data60, o, i64 1]
    out := out ++ mkRows "OP_SUBSTR" 0xb3 (fun p => chronicleGate p opSubstr) (fun p => chronicleGate p opSubstr122) (k + 1) s!"offset two; length {co}" [data60, i64 2, o]
    k := k + 2
  -- OP_NUM2BIN to one hundred million bytes: the model is not evaluated on this
  -- size; the expectation is the theorem `opNum2Bin_ok` (the result has exactly
  -- the requested length), and the row checks the length with OP_SIZE.
  let huge := i64 100000000
  for era in [Era.postChronicle, Era.postGenesis] do
    for relay in [false, true] do
      let word := if relay then "relay" else "block"
      let r : Row :=
        { id := "OP_NUM2BIN-huge-" ++ era.tag ++ "-" ++ word, era := era, opcode := "OP_NUM2BIN",
          covers := "size 100,000,000; expectation from opNum2Bin_ok, checked by OP_SIZE",
          spk := push (i64 1) ++ push huge ++ B [0x80, 0x82] ++ push huge ++ B [OP_EQUALVERIFY, OP_DROP, OP_1],
          flags := flagsOf era relay, expected := "OK", expected122 := "OK" }
      out := out ++ [r]
  out := out ++ (mkRows "OP_NUM2BIN" 0x80 opNum2Bin (same opNum2Bin) 100000
    "size 100,000,000 on an output from before Genesis" [i64 1, huge]).filter
      (fun r => r.era == Era.preGenesis)
  return out

/-! ## Slice 2: OP_LSHIFTNUM and OP_RSHIFTNUM -/

def errNameS : ShiftErr → String
  | .base e => errName e
  | .bigInt => "BIG_INT"

def mkRowsS (opname : String) (opbyte : Nat) (op : Params → Stack → Except ShiftErr Stack)
    (idx : Nat) (covers : String) (args : List Elem) : List Row :=
  [Era.postChronicle, Era.postGenesis, Era.preGenesis].flatMap fun era =>
  [false, true].map fun relay =>
    let p := paramsOf era relay
    let res := op p args.reverse
    let tail := match res with
      | .ok st => st.flatMap (fun e => push e ++ B [OP_EQUALVERIFY]) ++ B [OP_1]
      | .error _ => B [OP_DROP, OP_1]
    let v := match res with
      | .ok _ => "OK"
      | .error e => errNameS e
    { id := s!"{opname}-{idx}-{era.tag}-{if relay then "relay" else "block"}", era := era,
      opcode := opname, covers := covers,
      spk := args.flatMap push ++ B [opbyte] ++ tail,
      flags := flagsOf era relay, expected := v, expected122 := "" }

def pow2 (k : Nat) : Int := (2 : Int) ^ k

def shiftCounts : List (String × Elem) :=
  [ ("0", encInt 0), ("1", encInt 1), ("7", encInt 7), ("8", encInt 8), ("9", encInt 9),
    ("63", encInt 63), ("64", encInt 64), ("65", encInt 65), ("255", encInt 255),
    ("256", encInt 256), ("4096", encInt 4096),
    ("INT_MAX, the largest count OP_RSHIFTNUM takes", encInt 2147483647),
    ("INT_MAX + 1", encInt 2147483648), ("2^32", encInt (pow2 32)), ("2^63", encInt (pow2 63)),
    ("2^64", encInt (pow2 64)), ("-1", encInt (-1)), ("non-minimal one: 01 00", B [1, 0]),
    ("negative zero: 80", B [0x80]) ]

def shiftValues : List (String × Elem) :=
  [ ("0", encInt 0), ("1", encInt 1), ("-1", encInt (-1)), ("2", encInt 2), ("127", encInt 127),
    ("128", encInt 128), ("255", encInt 255), ("-255", encInt (-255)), ("256", encInt 256),
    ("INT32_MAX", encInt 2147483647), ("INT64_MAX", encInt (pow2 63 - 1)),
    ("INT64_MIN", encInt (-(pow2 63))), ("2^64", encInt (pow2 64)), ("2^70", encInt (pow2 70)),
    ("-(2^70)", encInt (-(pow2 70))), ("2^70 + 12345", encInt (pow2 70 + 12345)),
    ("-(2^70 + 12345)", encInt (-(pow2 70 + 12345))),
    ("non-minimal one: 01 00", B [1, 0]), ("negative zero: 80", B [0x80]),
    ("nine bytes, padded one", B [1, 0, 0, 0, 0, 0, 0, 0, 0]) ]

def shiftRows : List Row := Id.run do
  let mut out : List Row := []
  let mut k := 0
  for (cv, v) in shiftValues do
    for (cn, n) in shiftCounts do
      out := out ++ mkRowsS "OP_LSHIFTNUM" 0xb6 (fun p => chronicleGateS p opLShiftNum) k s!"{cv} << {cn}" [v, n]
      out := out ++ mkRowsS "OP_RSHIFTNUM" 0xb7 (fun p => chronicleGateS p opRShiftNum) k s!"{cv} >> {cn}" [v, n]
      k := k + 1
  return out

/-! ## Slice 3: OP_LSHIFT and OP_RSHIFT on byte strings -/

def byteShiftRows : List Row := Id.run do
  let same (f : Params → Stack → Except Err Stack) := f
  let elemsB : List (String × Elem) :=
    [ ("empty", []), ("80", B [0x80]), ("01", B [0x01]), ("ff", B [0xff]), ("01 02 03", B [1, 2, 3]),
      ("nine bytes of ff", B [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
      ("a5 5a c3 3c", B [0xa5, 0x5a, 0xc3, 0x3c]), ("sixty bytes", data60) ]
  let mut out : List Row := []
  let mut k := 0
  for (ce, e) in elemsB do
    let w := e.length * 8
    let counts : List (String × Elem) :=
      [ ("0", encInt 0), ("1", encInt 1), ("7", encInt 7), ("8", encInt 8), ("9", encInt 9),
        ("15", encInt 15), ("16", encInt 16), ("63", encInt 63), ("64", encInt 64), ("65", encInt 65),
        ("width - 1", encInt ((w : Int) - 1)), ("width", encInt w), ("width + 1", encInt ((w : Int) + 1)),
        ("INT32_MAX", encInt 2147483647), ("INT32_MAX + 1", encInt 2147483648),
        ("2^63", encInt (pow2 63)), ("2^64", encInt (pow2 64)), ("-1", encInt (-1)),
        ("non-minimal one: 01 00", B [1, 0]), ("negative zero: 80", B [0x80]) ]
    for (cn, n) in counts do
      out := out ++ mkRows "OP_LSHIFT" 0x98 opLShift (same opLShift) k s!"{ce} << {cn}" [e, n]
      out := out ++ mkRows "OP_RSHIFT" 0x99 opRShift (same opRShift) k s!"{ce} >> {cn}" [e, n]
      k := k + 1
  return out

/-! ## Slice 4: arithmetic and comparison opcodes -/

def arithOperands : List (String × Elem) :=
  [ ("0", encInt 0), ("1", encInt 1), ("-1", encInt (-1)), ("2", encInt 2), ("-3", encInt (-3)),
    ("7", encInt 7), ("INT32_MAX", encInt 2147483647), ("-INT32_MAX", encInt (-2147483647)),
    ("2^31, five bytes", encInt 2147483648), ("INT64_MAX", encInt (pow2 63 - 1)),
    ("INT64_MIN", encInt (-(pow2 63))), ("2^70 + 5", encInt (pow2 70 + 5)),
    ("negative zero: 80", B [0x80]), ("non-minimal one: 01 00", B [1, 0]) ]

def arithRows : Array Row := Id.run do
  let same (f : Params → Stack → Except Err Stack) := f
  let mut out : Array Row := #[]
  let unary : List (String × Nat × Unary) :=
    [ ("OP_1ADD", 0x8b, .add1), ("OP_1SUB", 0x8c, .sub1), ("OP_2MUL", 0x8d, .mul2),
      ("OP_2DIV", 0x8e, .div2), ("OP_NEGATE", 0x8f, .negate), ("OP_ABS", 0x90, .abs),
      ("OP_NOT", 0x91, .not), ("OP_0NOTEQUAL", 0x92, .notEqual0) ]
  for (name, byte, u) in unary do
    let mut k := 0
    for (c, a) in arithOperands do
      out := out ++ (mkRows name byte (opUnary u) (same (opUnary u)) k c [a]).toArray
      k := k + 1
  let binary : List (String × Nat × Binary) :=
    [ ("OP_ADD", 0x93, .add), ("OP_SUB", 0x94, .sub), ("OP_MUL", 0x95, .mul), ("OP_DIV", 0x96, .div),
      ("OP_MOD", 0x97, .mod), ("OP_BOOLAND", 0x9a, .boolAnd), ("OP_BOOLOR", 0x9b, .boolOr),
      ("OP_NUMEQUAL", 0x9c, .numEqual), ("OP_NUMEQUALVERIFY", 0x9d, .numEqualVerify),
      ("OP_NUMNOTEQUAL", 0x9e, .numNotEqual), ("OP_LESSTHAN", 0x9f, .lt),
      ("OP_GREATERTHAN", 0xa0, .gt), ("OP_LESSTHANOREQUAL", 0xa1, .le),
      ("OP_GREATERTHANOREQUAL", 0xa2, .ge), ("OP_MIN", 0xa3, .min), ("OP_MAX", 0xa4, .max) ]
  for (name, byte, b) in binary do
    let mut k := 0
    for (c1, a) in arithOperands do
      for (c2, c) in arithOperands do
        out := out ++ (mkRows name byte (opBinary b) (same (opBinary b)) k s!"{c1} , {c2}" [a, c]).toArray
        k := k + 1
  let mut k := 0
  for (c1, a) in arithOperands.take 8 do
    for (c2, lo) in [("-1", encInt (-1)), ("0", encInt 0), ("2", encInt 2), ("negative zero", B [0x80])] do
      for (c3, hi) in [("0", encInt 0), ("2", encInt 2), ("INT32_MAX", encInt 2147483647), ("2^31", encInt 2147483648)] do
        out := out ++ (mkRows "OP_WITHIN" 0xa5 opWithin (same opWithin) k s!"{c1} in [{c2}, {c3})" [a, lo, hi]).toArray
        k := k + 1
  return out

def emit (source : String) (rs : List Row) : IO UInt32 := do
  IO.println ("{\"source\": \"bsv-lean-proofs, generated from " ++ source ++
    " (model of bitcoin-sv v1.2.3); expected = the model's verdict\",")
  IO.println " \"version\": 1,"
  IO.println " \"cases\": ["
  let n := rs.length
  for (i, r) in (List.range n).zip rs do
    IO.println ("  " ++ r.json ++ (if i + 1 < n then "," else ""))
  IO.println " ]}"
  return 0

def main (args : List String) : IO UInt32 := do
  if args == ["arith"] then
    return ← emit "BsvLeanProofs.Arith" arithRows.toList
  if args == ["byteshift"] then
    return ← emit "BsvLeanProofs.ByteShift" byteShiftRows
  if args == ["shift"] then
    IO.println "{\"source\": \"bsv-lean-proofs, generated from BsvLeanProofs.ShiftNum (model of bitcoin-sv v1.2.3); expected = the model's verdict\","
    IO.println " \"version\": 1,"
    IO.println " \"cases\": ["
    let rs := shiftRows
    let n := rs.length
    for (i, r) in (List.range n).zip rs do
      IO.println ("  " ++ r.json ++ (if i + 1 < n then "," else ""))
    IO.println " ]}"
    return 0
  IO.println "{\"source\": \"bsv-lean-proofs, generated from BsvLeanProofs.Splice (model of bitcoin-sv v1.2.3); expected = the model's verdict\","
  IO.println " \"version\": 2,"
  IO.println " \"cases\": ["
  let rs := rows
  let n := rs.length
  for (i, r) in (List.range n).zip rs do
    IO.println ("  " ++ r.json ++ (if i + 1 < n then "," else ""))
  IO.println " ]}"
  return 0
