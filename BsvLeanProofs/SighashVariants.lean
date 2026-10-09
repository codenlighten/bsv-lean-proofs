import BsvLeanProofs.SighashCommit

/-!
# The other signature-hash types: what they fix and what they leave open

Same model and same assumptions as `SighashCommit` (the modelled fork-id
digest; the hash a parameter with 32-byte output; serialization assumed).

Fixed:
* `digest_fixes_signed_input`: every type fixes the version, the signed input's
  outpoint and sequence number, the script code, the amount, the lock time and
  the type bytes, or the two preimages collide.
* `digest_fixes_outputs`: base type ALL fixes all outputs, with or without
  ANYONECANPAY, or a named pair collides.
* `digest_single_fixes_output`: base type SINGLE, with the input index inside
  both output lists, fixes the output at that index, or a named pair collides.

Left open (equalities of digests, no hash assumption at all):
* `digest_none_ignores_outputs`: base type NONE does not read the outputs.
* `digest_single_ignores_other_outputs`: SINGLE does not read the outputs at
  other indices, provided the list still reaches the signed index.
* `digest_single_out_of_range`: SINGLE with the input index beyond the outputs
  reads no output at all.
* `digest_acp_ignores_other_inputs`: ANYONECANPAY reads only the signed input.
-/

namespace Bsv.Sighash

open Bsv.ScriptNum

theorem digest_fixes_signed_input (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32)
    (tx tx' : Tx) (htx : tx.WF) (htx' : tx'.WF) (i : Nat) (hi : i < tx.ins.length)
    (hi' : i < tx'.ins.length) (sc sc' amount amount' ty ty' : List Byte)
    (hsc : sc.length < 18446744073709551616) (hsc' : sc'.length < 18446744073709551616)
    (ham : amount.length = 8) (ham' : amount'.length = 8) (hty : ty.length = 4) (hty' : ty'.length = 4)
    (h : digest H tx i sc amount ty = digest H tx' i sc' amount' ty') :
    (tx.version = tx'.version ∧ tx.ins.getD i ([], []) = tx'.ins.getD i ([], []) ∧ sc = sc' ∧
      amount = amount' ∧ tx.lockTime = tx'.lockTime ∧ ty = ty') ∨
    CollisionAt H (preOf H tx i sc amount ty).bytes (preOf H tx' i sc' amount' ty').bytes := by
  rcases digest_fixes_fields H hlen tx tx' htx htx' i hi hi' sc sc' amount amount' ty ty'
    hsc hsc' ham ham' hty hty' h with hp | hc
  · simp only [preOf, Pre.mk.injEq] at hp
    obtain ⟨ev, -, -, e1, esc, eam, e2, -, el, ety⟩ := hp
    exact .inl ⟨ev, Prod.ext e1 e2, esc, eam, el, ety⟩
  · exact .inr hc

theorem digest_fixes_outputs (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32)
    (tx tx' : Tx) (htx : tx.WF) (htx' : tx'.WF) (i : Nat) (hi : i < tx.ins.length)
    (hi' : i < tx'.ins.length) (sc sc' amount amount' ty : List Byte)
    (hsc : sc.length < 18446744073709551616) (hsc' : sc'.length < 18446744073709551616)
    (ham : amount.length = 8) (ham' : amount'.length = 8) (hty : ty.length = 4)
    (hall : (baseType (ty.headD 0#8) != 2 && baseType (ty.headD 0#8) != 3) = true)
    (h : digest H tx i sc amount ty = digest H tx' i sc' amount' ty) :
    tx.outs = tx'.outs ∨
    CollisionAt H (preOf H tx i sc amount ty).bytes (preOf H tx' i sc' amount' ty).bytes ∨
    CollisionAt H (tx.outs.map serOut).flatten (tx'.outs.map serOut).flatten := by
  rcases digest_fixes_fields H hlen tx tx' htx htx' i hi hi' sc sc' amount amount' ty ty
    hsc hsc' ham ham' hty hty h with hp | hc
  · simp only [preOf, hall, Pre.mk.injEq, ↓reduceIte] at hp
    obtain ⟨-, -, -, -, -, -, -, eo, -, -⟩ := hp
    by_cases c : (tx.outs.map serOut).flatten = (tx'.outs.map serOut).flatten
    · exact .inl (serOuts_inj _ _ htx.outs htx'.outs c)
    · exact .inr (.inr ⟨c, eo⟩)
  · exact .inr (.inl hc)

theorem digest_single_fixes_output (H : List Byte → List Byte) (hlen : ∀ x, (H x).length = 32)
    (tx tx' : Tx) (htx : tx.WF) (htx' : tx'.WF) (i : Nat) (hi : i < tx.ins.length)
    (hi' : i < tx'.ins.length) (sc sc' amount amount' ty : List Byte)
    (hsc : sc.length < 18446744073709551616) (hsc' : sc'.length < 18446744073709551616)
    (ham : amount.length = 8) (ham' : amount'.length = 8) (hty : ty.length = 4)
    (hsingle : baseType (ty.headD 0#8) = 3)
    (ho : i < tx.outs.length) (ho' : i < tx'.outs.length)
    (h : digest H tx i sc amount ty = digest H tx' i sc' amount' ty) :
    tx.outs.getD i ([], []) = tx'.outs.getD i ([], []) ∨
    CollisionAt H (preOf H tx i sc amount ty).bytes (preOf H tx' i sc' amount' ty).bytes ∨
    CollisionAt H (serOut (tx.outs.getD i ([], []))) (serOut (tx'.outs.getD i ([], []))) := by
  rcases digest_fixes_fields H hlen tx tx' htx htx' i hi hi' sc sc' amount amount' ty ty
    hsc hsc' ham ham' hty hty h with hp | hc
  · simp only [preOf, hsingle, Pre.mk.injEq, ho, ho', decide_true] at hp
    obtain ⟨-, -, -, -, -, -, -, eo, -, -⟩ := hp
    have eo' : H (serOut (tx.outs.getD i ([], []))) = H (serOut (tx'.outs.getD i ([], []))) := by
      simpa using eo
    by_cases c : serOut (tx.outs.getD i ([], [])) = serOut (tx'.outs.getD i ([], []))
    · have w : (tx.outs.getD i ([], [])).WF := htx.outs _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]; simp)
      have w' : (tx'.outs.getD i ([], [])).WF := htx'.outs _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho']; simp)
      exact .inl (serOut_inj _ _ [] [] w w' (by simpa using c)).1
    · exact .inr (.inr ⟨c, eo'⟩)
  · exact .inr (.inl hc)

/-! ## What the other types do not read -/

theorem digest_none_ignores_outputs (H : List Byte → List Byte) (tx : Tx) (outs' : List Out)
    (i : Nat) (sc amount ty : List Byte) (hnone : baseType (ty.headD 0#8) = 2) :
    digest H { tx with outs := outs' } i sc amount ty = digest H tx i sc amount ty := by
  simp only [digest, preOf, hnone]
  simp

theorem digest_single_out_of_range (H : List Byte → List Byte) (tx : Tx) (outs' : List Out)
    (i : Nat) (sc amount ty : List Byte) (hsingle : baseType (ty.headD 0#8) = 3)
    (ho : tx.outs.length ≤ i) (ho' : outs'.length ≤ i) :
    digest H { tx with outs := outs' } i sc amount ty = digest H tx i sc amount ty := by
  have h1 : ¬ i < tx.outs.length := by omega
  have h2 : ¬ i < outs'.length := by omega
  simp only [digest, preOf, hsingle, h1, h2]
  simp

theorem digest_single_ignores_other_outputs (H : List Byte → List Byte) (tx : Tx)
    (outs' : List Out) (i : Nat) (sc amount ty : List Byte)
    (hsingle : baseType (ty.headD 0#8) = 3)
    (ho : i < tx.outs.length) (ho' : i < outs'.length)
    (hsame : outs'.getD i ([], []) = tx.outs.getD i ([], [])) :
    digest H { tx with outs := outs' } i sc amount ty = digest H tx i sc amount ty := by
  simp only [digest, preOf, hsingle, ho, ho', hsame]
  simp

/-- With ANYONECANPAY and base type NONE or SINGLE the other inputs are not
read at all; with base type ALL the same holds, by the same computation. -/
theorem digest_acp_ignores_other_inputs (H : List Byte → List Byte) (tx : Tx) (ins' : List In)
    (i : Nat) (sc amount ty : List Byte) (hacp : anyoneCanPay (ty.headD 0#8) = true)
    (hsame : ins'.getD i ([], []) = tx.ins.getD i ([], [])) :
    digest H { tx with ins := ins' } i sc amount ty = digest H tx i sc amount ty := by
  simp only [digest, preOf, hacp, hsame]
  simp

end Bsv.Sighash
