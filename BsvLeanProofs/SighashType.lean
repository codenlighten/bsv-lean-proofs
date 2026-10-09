/-!
# The sighash-type check: go-sdk before and after issue #373, and the node

Models of
* `thread.checkHashTypeEncoding` in go-sdk v1.7.0 (`script/interpreter/thread.go`),
  which accepted a signature without the ForkID bit under
  `VerifyStrictEncoding | EnableSighashForkID`;
* the same function on go-sdk master at commit 511b58ce (after PR #374);
* the STRICTENC block of `CheckSignatureEncoding` in bitcoin-sv v1.2.2
  (`src/script/interpreter.cpp`, with `SigHashType::isDefined`).

What is modelled: the decision as a function of the sighash-type byte and the
flags the function reads. What is not: everything else about a signature (DER
form, low S, the empty signature), and how the callers set the flags. The node
keeps the hash type in 32 bits; it is read from one byte, so 8 bits are used.

Tested against the source (`difftest/run_gosdk.sh`): both go-sdk functions,
executed on every byte and every setting of the four flags each reads, return
exactly what `check170` and `checkMaster` return. The node model is compared with a
compiled v1.2.2 `VerifyScript` by `difftest/node_hashtype.py`, through
`nodeVerifyScript` below.
-/

namespace Bsv.SighashType

set_option maxRecDepth 100000

abbrev Flag := BitVec 8

def all : Flag := 0x01
def single : Flag := 0x03
def chronicle : Flag := 0x20
def forkID : Flag := 0x40
def anyOneCanPay : Flag := 0x80

/-- `Flag.Has`. -/
def has (f g : Flag) : Bool := f &&& g == g

inductive Verdict
  | accept
  | invalidSigHashType
  | illegalForkID
  | illegalChronicle
  | mustUseForkID
  deriving DecidableEq, Repr

open Verdict

/-- go-sdk v1.7.0. `afterChronicle` is the thread's era field. -/
def check170 (strict bip143 forkIDEnabled afterChronicle : Bool) (shf : Flag) : Verdict :=
  if !strict then accept else
  let t := shf &&& ~~~anyOneCanPay
  let t := if afterChronicle && has shf forkID then t &&& ~~~chronicle else t
  let t := if bip143 then t ^^^ forkID else t
  if bip143 && shf &&& forkID == 0 then invalidSigHashType else
  if !has t forkID then
    if t.ult all || single.ult t then invalidSigHashType else accept
  else
  if t.ult (all ||| forkID) || (single ||| forkID).ult t then invalidSigHashType else
  if !forkIDEnabled && has shf forkID then illegalForkID else
  if forkIDEnabled && !has shf forkID then illegalForkID else
  accept

/-- go-sdk master at 511b58ce. -/
def checkMaster (strict bip143 forkIDEnabled chronicleEnabled : Bool) (shf : Flag) : Verdict :=
  if !strict then accept else
  let t := shf &&& ~~~anyOneCanPay
  if bip143 then
    let t := t ^^^ forkID
    if shf &&& forkID == 0 then invalidSigHashType else
    if t.ult all || single.ult t then invalidSigHashType else accept
  else
  let base := t &&& ~~~forkID &&& ~~~chronicle
  if base.ult all || single.ult base then invalidSigHashType else
  if !forkIDEnabled && has shf forkID then illegalForkID else
  if !chronicleEnabled && has shf chronicle then illegalChronicle else
  if forkIDEnabled && !has shf forkID then mustUseForkID else
  accept

/-- bitcoin-sv v1.2.2, the STRICTENC block of `CheckSignatureEncoding`. -/
def checkNode (strict forkIDEnabled chronicleEnabled : Bool) (shf : Flag) : Verdict :=
  if !strict then accept else
  let base := shf &&& ~~~(chronicle ||| forkID ||| anyOneCanPay)
  if !(all.ule base && base.ule single) then invalidSigHashType else
  if !forkIDEnabled && shf &&& forkID != 0 then illegalForkID else
  if !chronicleEnabled && shf &&& chronicle != 0 then illegalChronicle else
  if forkIDEnabled && shf &&& forkID == 0 then mustUseForkID else
  accept

/-- A statement about every byte follows from checking the 256 values. -/
theorem forall_flag {P : Flag → Prop} (h : ∀ n : Fin 256, P (BitVec.ofFin n)) : ∀ f : Flag, P f :=
  fun f => h f.toFin

/-- **The fix.** On master, under strict encoding with ForkID enabled, no
sighash-type byte without the ForkID bit is accepted, whatever the other two
flags are. -/
theorem master_rejects_missing_forkID :
    ∀ (bip143 chronicleEnabled : Bool) (shf : Flag),
      has shf forkID = false → checkMaster true bip143 true chronicleEnabled shf ≠ accept := by
  intro b c
  apply forall_flag
  revert b c
  decide

/-- **The bug.** In v1.7.0, under the same flags (and without the
conformance-only `VerifyBip143SigHash` flag), a byte without the ForkID bit is
accepted exactly when removing AnyOneCanPay leaves 01, 02 or 03: the six bytes
01, 02, 03, 81, 82, 83. -/
theorem v170_accepts_missing_forkID :
    ∀ (afterChronicle : Bool) (shf : Flag),
      (has shf forkID = false ∧ check170 true false true afterChronicle shf = accept) ↔
      (shf = 0x01 ∨ shf = 0x02 ∨ shf = 0x03 ∨ shf = 0x81 ∨ shf = 0x82 ∨ shf = 0x83) := by
  intro a
  apply forall_flag
  revert a
  decide

/-- **Agreement with the node.** Without `VerifyBip143SigHash`, master returns
the node's verdict, in the five categories of `Verdict`, for every byte and
every setting of the three flags. This compares the two modelled decisions
only; it says nothing about how each caller sets its flags. -/
theorem master_eq_node :
    ∀ (strict forkIDEnabled chronicleEnabled : Bool) (shf : Flag),
      checkMaster strict false forkIDEnabled chronicleEnabled shf =
        checkNode strict forkIDEnabled chronicleEnabled shf := by
  intro a b c
  apply forall_flag
  revert a b c
  decide

/-- The node rejects every byte without the ForkID bit under strict encoding
with ForkID enabled, so each of the six bytes above was a false accept. -/
theorem node_rejects_missing_forkID :
    ∀ (chronicleEnabled : Bool) (shf : Flag),
      has shf forkID = false → checkNode true true chronicleEnabled shf ≠ accept := by
  intro c
  apply forall_flag
  revert c
  decide

/-- With `VerifyBip143SigHash` set, master does not follow the node. Example:
byte 0x61 (ALL | FORKID | CHRONICLE) with ForkID and Chronicle both enabled is
accepted by the node and refused by master. -/
example : checkNode true true true 0x61 = accept ∧
    checkMaster true true true true 0x61 = invalidSigHashType := by decide

/-! ## One step out: the flag the callers force

`VerifyScript` in the node sets STRICTENC whenever SIGHASH_FORKID is enabled
(`interpreter.cpp`, "If FORKID is enabled, we also ensure strict encoding"),
and go-sdk's thread setup does the same in both versions. So with ForkID
enabled the check runs whether or not the caller asked for strict encoding.
Only this one implication is modelled; the other flag derivations (for example
master's "the era of the spent output implies the era of the spend") are not. -/

def nodeVerifyScript (strict forkIDEnabled chronicleEnabled : Bool) (shf : Flag) : Verdict :=
  checkNode (strict || forkIDEnabled) forkIDEnabled chronicleEnabled shf

def masterThread (strict bip143 forkIDEnabled chronicleEnabled : Bool) (shf : Flag) : Verdict :=
  checkMaster (strict || forkIDEnabled) bip143 forkIDEnabled chronicleEnabled shf

def v170Thread (strict bip143 forkIDEnabled afterChronicle : Bool) (shf : Flag) : Verdict :=
  check170 (strict || forkIDEnabled) bip143 forkIDEnabled afterChronicle shf

/-- With ForkID enabled the node rejects every byte without the ForkID bit,
whether or not strict encoding was requested. -/
theorem nodeVerifyScript_rejects_missing_forkID :
    ∀ (strict chronicleEnabled : Bool) (shf : Flag),
      has shf forkID = false → nodeVerifyScript strict true chronicleEnabled shf ≠ accept := by
  intro a c
  apply forall_flag
  revert a c
  decide

/-- So does go-sdk master. -/
theorem masterThread_rejects_missing_forkID :
    ∀ (strict bip143 chronicleEnabled : Bool) (shf : Flag),
      has shf forkID = false → masterThread strict bip143 true chronicleEnabled shf ≠ accept := by
  intro a b c
  apply forall_flag
  revert a b c
  decide

/-- And v1.7.0 accepted the same six bytes with ForkID enabled alone: the
false accept did not need the caller to set strict encoding. -/
theorem v170Thread_accepts_missing_forkID :
    ∀ (strict afterChronicle : Bool) (shf : Flag),
      (has shf forkID = false ∧ v170Thread strict false true afterChronicle shf = accept) ↔
      (shf = 0x01 ∨ shf = 0x02 ∨ shf = 0x03 ∨ shf = 0x81 ∨ shf = 0x82 ∨ shf = 0x83) := by
  intro s a
  apply forall_flag
  revert s a
  decide

/-- With the forced flag, master still returns the node's verdict whenever
`VerifyBip143SigHash` is off. -/
theorem masterThread_eq_nodeVerifyScript :
    ∀ (strict forkIDEnabled chronicleEnabled : Bool) (shf : Flag),
      masterThread strict false forkIDEnabled chronicleEnabled shf =
        nodeVerifyScript strict forkIDEnabled chronicleEnabled shf := by
  intro a b c
  apply forall_flag
  revert a b c
  decide

end Bsv.SighashType
