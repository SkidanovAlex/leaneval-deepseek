import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **`eq:DefT`'s third (large-momentum) row, summed over the slots.**  `momWord` is `nPlusHB`'s
per-slot momentum form `momForm` times the constant `b ε_T (dℓ)⁻²`, so the slot sum is that
constant times the `ℓ³`-scaled slot sum appearing in the definition of `nPlusHB`.  The only
content is linearity of the (unconditional Bochner) integral in the constant factor and of the
finite sum, plus `ℓ³ · ℓ⁻³ = 1` (`hℓ`). -/
theorem momRowSum {ℓ d eT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.momWord ℓ d eT b 0 (Work.BoseKinLoc.fibre n i Φ x))
      = b * eT * (d * ℓ) ^ (-2 : ℤ) * (ℓ ^ 3 * Work.BoseBoxFix.nPlusHB ℓ d Φ) := by
  -- Pull the constant `b ε_T (dℓ)⁻²` out of the `i`-th slot integral.
  have hc : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * (b * eT * (d * ℓ) ^ (-2 : ℤ)
              * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n i Φ x)))
      = b * eT * (d * ℓ) ^ (-2 : ℤ) *
          (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n i Φ x)) := by
    intro i
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  simp only [Work.BoseKinLoc.momWord, Work.BoseBoxFix.nPlusHB]
  trans (∑ i : Fin n, b * eT * (d * ℓ) ^ (-2 : ℤ) *
          (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n i Φ x)))
  · exact Finset.sum_congr rfl (fun i _ => hc i)
  · -- Pull the constant out of the finite sum, then cancel `ℓ³ · ℓ⁻³`.
    rw [← Finset.mul_sum]
    congr 1
    have h3 : ℓ ^ (-3 : ℤ) = (ℓ ^ 3)⁻¹ := by
      rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    rw [h3, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

end Work.BoseBoxFock
