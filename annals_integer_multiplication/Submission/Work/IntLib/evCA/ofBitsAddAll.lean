import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `ofBits` of the left-to-right bit addition `EvC.addAll`

`EvC.addAll W hbits` is the bit list (least significant bit first) produced by the single
left-to-right ripple scan of `EvC.evCarryProg`: at each step `k` the two stream bits
`W.getD k false` and `hbits.getD k false` and the running carry are added, the sum bit is
emitted (`EvC.accF`) and the new carry recorded (`EvC.carryC`); after
`EvC.addN W hbits = max |W| |hbits|` steps the final carry (if any) is emitted as the top bit.

The arithmetic content is the invariant
`ofBits (accF … k) + 2^k * (ofBits (W.drop k) + ofBits (hbits.drop k) + (carryC … k).toNat)
  = ofBits W + ofBits hbits + c0.toNat`:
"the value emitted so far, plus `2^k` times the value still to be processed".  It is preserved
by one ripple step because `sumBit a b c + 2 * carryBit a b c = a + b + c`
(`EvC.toNat_sumBit_add_carry`).
-/

set_option autoImplicit false

open Work.IntLib Work.IntLib.EvC

namespace Work.IntLib.EvC

/-- The invariant of the left-to-right bit addition: after `k` ripple steps the emitted bits
`accF … k` together with `2^k` times the not-yet-processed parts of the two streams and the
carry represent the total `ofBits W + ofBits hbits + c0.toNat`. -/
theorem ofBits_accF_add_carryC (W hbits : List Bool) (c0 : Bool) (k : ℕ) :
    ofBits (accF W hbits c0 k) +
        2 ^ k * (ofBits (W.drop k) + ofBits (hbits.drop k) + (carryC W hbits c0 k).toNat)
      = ofBits W + ofBits hbits + c0.toNat := by
  induction k with
  | zero => simp [accF, carryC, ofBits]
  | succ k ih =>
    have hstep : ofBits (accF W hbits c0 (k+1)) +
        2 ^ (k+1) * (ofBits (W.drop (k+1)) + ofBits (hbits.drop (k+1)) +
          (carryC W hbits c0 (k+1)).toNat)
        = ofBits (accF W hbits c0 k) +
          2 ^ k * (ofBits (W.drop k) + ofBits (hbits.drop k) + (carryC W hbits c0 k).toNat) := by
      have hsc := toNat_sumBit_add_carry (W.getD k false) (hbits.getD k false) (carryC W hbits c0 k)
      rw [accF, carryC, ofBits_append_singleton, accF_length, ofBits_drop_eq W k,
        ofBits_drop_eq hbits k]
      rw [pow_succ, Nat.add_assoc, Nat.add_left_cancel_iff]
      rw [Nat.mul_assoc, ← Nat.mul_add]
      congr 1
      omega
    rw [hstep, ih]

end Work.IntLib.EvC

namespace Work.IntLib.evCA

theorem ofBitsAddAll (W hbits : List Bool) :
    Work.IntLib.ofBits (Work.IntLib.EvC.addAll W hbits) = Work.IntLib.ofBits W + Work.IntLib.ofBits hbits := by
  have hW : W.drop (addN W hbits) = [] := List.drop_eq_nil_of_le (le_max_left _ _)
  have hB : hbits.drop (addN W hbits) = [] := List.drop_eq_nil_of_le (le_max_right _ _)
  have H := ofBits_accF_add_carryC W hbits false (addN W hbits)
  rw [hW, hB, show ofBits ([] : List Bool) = 0 from rfl] at H
  simp only [Nat.zero_add, Bool.toNat_false, Nat.add_zero] at H
  by_cases hc : carryC W hbits false (addN W hbits) = true
  · rw [addAll]
    simp only [hc, ite_true]
    rw [hc, Bool.toNat_true] at H
    simp only [Nat.mul_one] at H
    rw [ofBits_append_singleton, accF_length]
    simp only [Bool.toNat_true, Nat.mul_one]
    exact H
  · rw [addAll]
    rw [Bool.not_eq_true] at hc
    simp only [hc]
    rw [hc] at H
    simpa using H

end Work.IntLib.evCA
