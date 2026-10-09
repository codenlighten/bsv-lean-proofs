import BsvLeanProofs.SighashPreimage

/-!
# A collision reduction for the fork-id signature digest

A model of `SignatureHashBIP143` (bitcoin-sv v1.2.3) at the level of a
transaction's fields, and theorems saying which of those fields two
transactions must share if their digests are equal and no collision occurs.

What the model is. A transaction here is only what the digest reads: version,
each input's outpoint and sequence number, the outputs, and the lock time. The
inputs' unlocking scripts are not in it, because the digest does not read them.
The script code and the amount are separate arguments; nothing here says how
the node obtains them. The theorems are about this modelled digest: they say
nothing about a signature, and they are a statement about the node only as far
as the serialization assumed below is the node's.

Assumed, not proved: that `ss << x` in the source writes an outpoint as 36
bytes, an output as its 8-byte value followed by its script with a CompactSize
length, the script code with a CompactSize length, and the type as 4 bytes
whose first holds the base type and the ANYONECANPAY bit; and that the node's
cached inner hashes equal the computed ones.

The hash function is a parameter `H`, about which the theorems assume only
that its output is 32 bytes. They do NOT assume it is injective: no function
with a fixed-length output is, so such an assumption would make the theorems
empty. Instead each conclusion is a disjunction: the two transactions agree on
the listed parts, OR one of a short list of NAMED pairs of strings, built from
the two transactions, is a collision of `H`. That is the reduction a
collision-resistance argument needs.

* `digest_fixes_fields`: for every signature-hash type, equal digests give the
  same preimage fields (version, the signed input's outpoint and sequence
  number, script code, amount, lock time, type bytes and the three inner
  hashes), or the two preimages collide.
* `digest_all_fixes_tx`: for the base type ALL without ANYONECANPAY, equal
  digests give the same outpoints and sequence numbers for every input and the
  same outputs, or one of four named pairs collides.

Not covered: the original (non-fork-id) digest, used when the fork-id bit is
absent or the Chronicle bit is present; the NONE, SINGLE and ANYONECANPAY
variants beyond `digest_fixes_fields`; and the encoding of the signature itself.
-/

namespace Bsv.Sighash

open Bsv.ScriptNum

/-- Concatenating items of one fixed positive width loses nothing. -/
theorem flatten_fixed_inj (w : Nat) (hw : 0 < w) : ∀ (a b : List (List Byte)),
    (∀ x ∈ a, x.length = w) → (∀ x ∈ b, x.length = w) → a.flatten = b.flatten → a = b
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hb, h => by
    have hy := hb y (by simp)
    have := congrArg List.length h
    simp only [List.flatten_cons, List.length_append, List.flatten_nil, List.length_nil] at this
    omega
  | x :: xs, [], ha, _, h => by
    have hx := ha x (by simp)
    have := congrArg List.length h
    simp only [List.flatten_cons, List.length_append, List.flatten_nil, List.length_nil] at this
    omega
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [List.flatten_cons] at h
    have hx := ha x (by simp)
    have hy := hb y (by simp)
    obtain ⟨e1, e2⟩ := List.append_inj h (by rw [hx, hy])
    have := flatten_fixed_inj w hw xs ys (fun z hz => ha z (by simp [hz]))
      (fun z hz => hb z (by simp [hz])) e2
    rw [e1, this]

theorem eq_of_maps : ∀ (a b : List (List Byte × List Byte)),
    a.map (·.1) = b.map (·.1) → a.map (·.2) = b.map (·.2) → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    rw [Prod.ext h1.1 h2.1, eq_of_maps xs ys h1.2 h2.2]

/-- An output: its 8-byte value and its locking script. -/
abbrev Out := List Byte × List Byte

def serOut (o : Out) : List Byte := o.1 ++ (varint o.2.length ++ o.2)

def Out.WF (o : Out) : Prop := o.1.length = 8 ∧ o.2.length < 18446744073709551616

theorem serOut_inj (a b : Out) (x y : List Byte) (ha : a.WF) (hb : b.WF)
    (h : serOut a ++ x = serOut b ++ y) : a = b ∧ x = y := by
  simp only [serOut, List.append_assoc] at h
  obtain ⟨e1, h⟩ := List.append_inj h (by rw [ha.1, hb.1])
  obtain ⟨el, h⟩ := varint_prefix _ _ _ _ ha.2 hb.2 h
  obtain ⟨e2, h⟩ := List.append_inj h el
  exact ⟨Prod.ext e1 e2, h⟩

/-- Serialized outputs are self-delimiting, so their concatenation loses nothing. -/
theorem serOuts_inj : ∀ (a b : List Out), (∀ o ∈ a, o.WF) → (∀ o ∈ b, o.WF) →
    (a.map serOut).flatten = (b.map serOut).flatten → a = b
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hb, h => by
    have hy := (hb y (by simp)).1
    have := congrArg List.length h
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.length_append, List.flatten_nil,
      List.length_nil, serOut] at this
    omega
  | x :: xs, [], ha, _, h => by
    have hx := (ha x (by simp)).1
    have := congrArg List.length h
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.length_append, List.flatten_nil,
      List.length_nil, serOut] at this
    omega
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨e1, e2⟩ := serOut_inj x y _ _ (ha x (by simp)) (hb y (by simp)) h
    have := serOuts_inj xs ys (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz])) e2
    rw [e1, this]

/-- An input as the digest sees it: its 36-byte outpoint and 4-byte sequence number. -/
abbrev In := List Byte × List Byte

structure Tx where
  version : List Byte
  ins : List In
  outs : List Out
  lockTime : List Byte

structure Tx.WF (tx : Tx) : Prop where
  version : tx.version.length = 4
  ins : ∀ i ∈ tx.ins, i.1.length = 36 ∧ i.2.length = 4
  outs : ∀ o ∈ tx.outs, o.WF
  lockTime : tx.lockTime.length = 4

def zero32 : List Byte := List.replicate 32 0#8

/-- The base type: 2 is NONE, 3 is SINGLE, anything else is treated as ALL. -/
def baseType (t : Byte) : Nat := (t &&& 0x1f#8).toNat
def anyoneCanPay (t : Byte) : Bool := t &&& 0x80#8 != 0#8

/-- The preimage fields `SignatureHashBIP143` assembles for input `i`. -/
def preOf (H : List Byte → List Byte) (tx : Tx) (i : Nat) (scriptCode amount ty : List Byte) : Pre :=
  let t := ty.headD 0#8
  let inp := tx.ins.getD i ([], [])
  { version := tx.version,
    hashPrevouts := if anyoneCanPay t then zero32 else H (tx.ins.map (·.1)).flatten,
    hashSequence :=
      if !anyoneCanPay t && baseType t != 2 && baseType t != 3
      then H (tx.ins.map (·.2)).flatten else zero32,
    prevout := inp.1, scriptCode := scriptCode, amount := amount, sequence := inp.2,
    hashOutputs :=
      if baseType t != 2 && baseType t != 3 then H (tx.outs.map serOut).flatten
      else if baseType t == 3 && decide (i < tx.outs.length) then H (serOut (tx.outs.getD i ([], [])))
      else zero32,
    lockTime := tx.lockTime, sigHashType := ty }

def digest (H : List Byte → List Byte) (tx : Tx) (i : Nat) (scriptCode amount ty : List Byte) :
    List Byte :=
  H (preOf H tx i scriptCode amount ty).bytes

theorem preOf_WF (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32) (tx : Tx)
    (htx : tx.WF) (i : Nat) (hi : i < tx.ins.length) (sc amount ty : List Byte)
    (hsc : sc.length < 18446744073709551616) (ham : amount.length = 8) (hty : ty.length = 4) :
    (preOf H tx i sc amount ty).WF := by
  have hin := htx.ins (tx.ins.getD i ([], [])) (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp)
  constructor
  · exact htx.version
  · simp only [preOf]; split <;> simp [zero32, hlen]
  · simp only [preOf]; split <;> simp [zero32, hlen]
  · exact hin.1
  · exact hsc
  · exact ham
  · exact hin.2
  · simp only [preOf]; split
    · simp [hlen]
    · split <;> simp [zero32, hlen]
  · exact htx.lockTime
  · exact hty

/-- Two different strings with the same hash. -/
def CollisionAt (H : List Byte → List Byte) (x y : List Byte) : Prop := x ≠ y ∧ H x = H y

/-- Equal digests fix the fields that every type signs, or the two preimages
are an explicit collision of `H`. -/
theorem digest_fixes_fields (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32)
    (tx tx' : Tx) (htx : tx.WF) (htx' : tx'.WF) (i : Nat) (hi : i < tx.ins.length)
    (hi' : i < tx'.ins.length) (sc sc' amount amount' ty ty' : List Byte)
    (hsc : sc.length < 18446744073709551616) (hsc' : sc'.length < 18446744073709551616)
    (ham : amount.length = 8) (ham' : amount'.length = 8) (hty : ty.length = 4) (hty' : ty'.length = 4)
    (h : digest H tx i sc amount ty = digest H tx' i sc' amount' ty') :
    preOf H tx i sc amount ty = preOf H tx' i sc' amount' ty' ∨
      CollisionAt H (preOf H tx i sc amount ty).bytes (preOf H tx' i sc' amount' ty').bytes := by
  by_cases hb : (preOf H tx i sc amount ty).bytes = (preOf H tx' i sc' amount' ty').bytes
  · exact .inl (bytes_injective _ _ (preOf_WF H hlen tx htx i hi sc amount ty hsc ham hty)
      (preOf_WF H hlen tx' htx' i hi' sc' amount' ty' hsc' ham' hty') hb)
  · exact .inr ⟨hb, h⟩

/-- Base type ALL without ANYONECANPAY: equal digests give the same version,
the same outpoints and sequence numbers for every input, the same script code
and amount, the same outputs and the same lock time, or one of four named
pairs of strings is a collision of `H`: the two preimages, the two outpoint
lists, the two sequence lists, or the two output lists. -/
theorem digest_all_fixes_tx (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32)
    (tx tx' : Tx) (htx : tx.WF) (htx' : tx'.WF) (i : Nat) (hi : i < tx.ins.length)
    (hi' : i < tx'.ins.length) (sc sc' amount amount' ty : List Byte)
    (hsc : sc.length < 18446744073709551616) (hsc' : sc'.length < 18446744073709551616)
    (ham : amount.length = 8) (ham' : amount'.length = 8) (hty : ty.length = 4)
    (hacp : anyoneCanPay (ty.headD 0#8) = false)
    (hall : (baseType (ty.headD 0#8) != 2 && baseType (ty.headD 0#8) != 3) = true)
    (h : digest H tx i sc amount ty = digest H tx' i sc' amount' ty) :
    (tx.version = tx'.version ∧ tx.ins = tx'.ins ∧ tx.outs = tx'.outs ∧
      tx.lockTime = tx'.lockTime ∧ sc = sc' ∧ amount = amount') ∨
    CollisionAt H (preOf H tx i sc amount ty).bytes (preOf H tx' i sc' amount' ty).bytes ∨
    CollisionAt H (tx.ins.map (·.1)).flatten (tx'.ins.map (·.1)).flatten ∨
    CollisionAt H (tx.ins.map (·.2)).flatten (tx'.ins.map (·.2)).flatten ∨
    CollisionAt H (tx.outs.map serOut).flatten (tx'.outs.map serOut).flatten := by
  rcases digest_fixes_fields H hlen tx tx' htx htx' i hi hi' sc sc' amount amount' ty ty
    hsc hsc' ham ham' hty hty h with hp | hc
  · simp only [preOf, hacp, Bool.not_false, Bool.true_and, hall, Pre.mk.injEq, Bool.false_eq_true,
      ↓reduceIte] at hp
    obtain ⟨ev, ep, es, -, esc, eam, -, eo, el, -⟩ := hp
    by_cases c1 : (tx.ins.map (·.1)).flatten = (tx'.ins.map (·.1)).flatten
    · by_cases c2 : (tx.ins.map (·.2)).flatten = (tx'.ins.map (·.2)).flatten
      · by_cases c3 : (tx.outs.map serOut).flatten = (tx'.outs.map serOut).flatten
        · have e1 := flatten_fixed_inj 36 (by omega) _ _
            (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx; exact (htx.ins a ha).1)
            (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx; exact (htx'.ins a ha).1)
            c1
          have e2 := flatten_fixed_inj 4 (by omega) _ _
            (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx; exact (htx.ins a ha).2)
            (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx; exact (htx'.ins a ha).2)
            c2
          have e3 := serOuts_inj _ _ htx.outs htx'.outs c3
          exact .inl ⟨ev, eq_of_maps _ _ e1 e2, e3, el, esc, eam⟩
        · exact .inr (.inr (.inr (.inr ⟨c3, eo⟩)))
      · exact .inr (.inr (.inr (.inl ⟨c2, es⟩)))
    · exact .inr (.inr (.inl ⟨c1, ep⟩))
  · exact .inr (.inl hc)

end Bsv.Sighash
