import BsvLeanProofs.ScriptNum

/-!
# The fork-id signature-hash preimage is injective in its fields

`SignatureHashBIP143` (bitcoin-sv v1.2.3, `src/script/interpreter.cpp`) hashes
the concatenation

    version(4) ‖ hashPrevouts(32) ‖ hashSequence(32) ‖ prevout(36) ‖
    CompactSize(len scriptCode) ‖ scriptCode ‖ amount(8) ‖ sequence(4) ‖
    hashOutputs(32) ‖ lockTime(4) ‖ sigHashType(4).

This file proves that the concatenation determines every field: two field
tuples with the same byte string are equal (`bytes_injective`). The only
variable-length field is `scriptCode`, and its CompactSize prefix is what makes
the layout unambiguous (`varint_prefix`).

Not claimed here: anything about SHA-256 (the digest of the preimage, and the
three inner hashes, are outside this file), and nothing about the original
(non-fork-id) digest, which is not injective: it returns the constant 1 for an
out-of-range SIGHASH_SINGLE.
-/

namespace Bsv.Sighash

open Bsv.ScriptNum

/-- `k` little-endian bytes of `n`. -/
def leBytes : Nat → Nat → List Byte
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 8 n :: leBytes k (n / 256)

def leVal : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

theorem length_leBytes : ∀ (k n : Nat), (leBytes k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [leBytes, length_leBytes k]

theorem leVal_leBytes : ∀ (k n : Nat), leVal (leBytes k n) = n % 256 ^ k
  | 0, n => by simp [leBytes, leVal, Nat.mod_one]
  | k + 1, n => by
    simp only [leBytes, leVal, leVal_leBytes k, BitVec.toNat_ofNat]
    rw [show (2 : Nat) ^ 8 = 256 from rfl,
      show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k from by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul]

theorem leBytes_inj (k n m : Nat) (x y : List Byte) (hn : n < 256 ^ k) (hm : m < 256 ^ k)
    (h : leBytes k n ++ x = leBytes k m ++ y) : n = m ∧ x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_leBytes, length_leBytes])
  have := congrArg leVal h1
  rw [leVal_leBytes, leVal_leBytes, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact ⟨this, h2⟩

/-- Bitcoin's CompactSize. -/
def varint (n : Nat) : List Byte :=
  if n < 0xfd then [BitVec.ofNat 8 n]
  else if n ≤ 0xffff then 0xfd#8 :: leBytes 2 n
  else if n ≤ 0xffffffff then 0xfe#8 :: leBytes 4 n
  else 0xff#8 :: leBytes 8 n

/-- A CompactSize prefix can be read off the front of a string unambiguously. -/
theorem varint_prefix (n m : Nat) (x y : List Byte)
    (hn : n < 18446744073709551616) (hm : m < 18446744073709551616)
    (h : varint n ++ x = varint m ++ y) : n = m ∧ x = y := by
  have p2 : (256 : Nat) ^ 2 = 65536 := by decide
  have p4 : (256 : Nat) ^ 4 = 4294967296 := by decide
  have p8 : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  unfold varint at h
  repeat' split at h
  all_goals
    simp only [List.cons_append, List.cons.injEq, List.nil_append] at h
    obtain ⟨hh, ht⟩ := h
    first
    | (exfalso; have hc := congrArg BitVec.toNat hh; revert hc; simp <;> omega)
    | (have hc := congrArg BitVec.toNat hh
       simp only [BitVec.toNat_ofNat] at hc
       exact ⟨by omega, ht⟩)
    | exact leBytes_inj 2 n m x y (by omega) (by omega) ht
    | exact leBytes_inj 4 n m x y (by omega) (by omega) ht
    | exact leBytes_inj 8 n m x y (by omega) (by omega) ht

/-- The fields of the preimage, as byte strings. -/
structure Pre where
  version : List Byte
  hashPrevouts : List Byte
  hashSequence : List Byte
  prevout : List Byte
  scriptCode : List Byte
  amount : List Byte
  sequence : List Byte
  hashOutputs : List Byte
  lockTime : List Byte
  sigHashType : List Byte

/-- The field widths the serialization fixes. -/
structure Pre.WF (p : Pre) : Prop where
  version : p.version.length = 4
  hashPrevouts : p.hashPrevouts.length = 32
  hashSequence : p.hashSequence.length = 32
  prevout : p.prevout.length = 36
  scriptCode : p.scriptCode.length < 18446744073709551616
  amount : p.amount.length = 8
  sequence : p.sequence.length = 4
  hashOutputs : p.hashOutputs.length = 32
  lockTime : p.lockTime.length = 4
  sigHashType : p.sigHashType.length = 4

/-- The byte string that is hashed. -/
def Pre.bytes (p : Pre) : List Byte :=
  p.version ++ (p.hashPrevouts ++ (p.hashSequence ++ (p.prevout ++
    (varint p.scriptCode.length ++ (p.scriptCode ++ (p.amount ++ (p.sequence ++
      (p.hashOutputs ++ (p.lockTime ++ p.sigHashType)))))))))

/-- Two well-formed field tuples with the same preimage are the same tuple. -/
theorem bytes_injective (a b : Pre) (ha : a.WF) (hb : b.WF) (h : a.bytes = b.bytes) : a = b := by
  simp only [Pre.bytes] at h
  obtain ⟨e1, h⟩ := List.append_inj h (by rw [ha.version, hb.version])
  obtain ⟨e2, h⟩ := List.append_inj h (by rw [ha.hashPrevouts, hb.hashPrevouts])
  obtain ⟨e3, h⟩ := List.append_inj h (by rw [ha.hashSequence, hb.hashSequence])
  obtain ⟨e4, h⟩ := List.append_inj h (by rw [ha.prevout, hb.prevout])
  obtain ⟨el, h⟩ := varint_prefix _ _ _ _ ha.scriptCode hb.scriptCode h
  obtain ⟨e5, h⟩ := List.append_inj h el
  obtain ⟨e6, h⟩ := List.append_inj h (by rw [ha.amount, hb.amount])
  obtain ⟨e7, h⟩ := List.append_inj h (by rw [ha.sequence, hb.sequence])
  obtain ⟨e8, h⟩ := List.append_inj h (by rw [ha.hashOutputs, hb.hashOutputs])
  obtain ⟨e9, e10⟩ := List.append_inj h (by rw [ha.lockTime, hb.lockTime])
  cases a; cases b
  simp_all

end Bsv.Sighash
