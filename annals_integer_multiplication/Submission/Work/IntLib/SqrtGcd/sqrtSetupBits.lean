import Mathlib
import Submission.Work.IntLib.SqrtGcd.Defs
import Submission.Work.IntLib.encodeNatBridge

namespace Work.IntLib.SqrtGcd

open Work.IntLib

/-- If `z ≥ 0`, the bit list which the `sqrt` setup is fed is the most-significant-first
encoding of `z.natAbs`, padded by one leading `false` when that encoding has odd length.
It therefore has even length and `SG.bval` it is exactly `z.toNat`:
the leading padding, if present, contributes `0`. -/
theorem sqrtSetupBits (z : ℤ) (hz : 0 ≤ z) (bs : List Bool)
    (hbs : bs = (if decide (z.natAbs.size % 2 = 1) then [false] else [])
        ++ (Computability.encodeNat z.natAbs).reverse) :
    bs.length % 2 = 0 ∧ Work.IntLib.SG.bval bs = z.toNat := by
  have hof : Work.IntLib.ofBits (Computability.encodeNat z.natAbs) = z.natAbs := by
    rw [Work.IntLib.encodeNat_eq_bits]; exact Work.IntLib.ofBits_bits _
  have hlen : (Computability.encodeNat z.natAbs).length = z.natAbs.size :=
    Work.IntLib.encodeNat_length _
  have hzt : z.toNat = z.natAbs := by omega
  rw [hbs, hzt]
  by_cases h : z.natAbs.size % 2 = 1
  · -- odd encoding: a leading `false` is prepended, making the length even
    have hif : (if decide (z.natAbs.size % 2 = 1) then [false] else ([] : List Bool)) = [false] := by
      simp [h]
    rw [hif]
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, List.length_reverse, hlen]; omega
    · rw [Work.IntLib.SG.bval_append, Work.IntLib.SG.bval_singleton]
      simp only [Work.IntLib.SG.bval, List.reverse_reverse]
      exact hof
  · -- even encoding: no padding
    have hif : (if decide (z.natAbs.size % 2 = 1) then [false] else ([] : List Bool)) = [] := by
      simp [h]
    rw [hif]
    refine ⟨?_, ?_⟩
    · have h2 : z.natAbs.size % 2 = 0 := by omega
      simp only [List.nil_append, List.length_reverse, hlen, h2]
    · simp only [List.nil_append, Work.IntLib.SG.bval, List.reverse_reverse]
      exact hof

end Work.IntLib.SqrtGcd
