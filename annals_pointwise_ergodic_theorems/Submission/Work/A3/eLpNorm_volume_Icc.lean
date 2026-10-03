import Mathlib
import Submission.Work.A3.Defs
import Submission.Port.Aesm

open MeasureTheory
open scoped ENNReal

namespace Work.A3

/-- The `ℒᵖ` seminorm of a function on the unit interval, for an exponent `r > 0`, is the `r`-th
root of the `r`-th power integral.  This is the form in which the `ℓᵖ`-improving estimates of the
`A3` area use the `Lᵖ` seminorm. -/
theorem eLpNorm_volume_Icc (h : ℝ → ℂ) (r : ℝ) (hr : 0 < r) (hint : MeasureTheory.Integrable (fun θ : ℝ => ‖h θ‖ ^ r) (MeasureTheory.volume.restrict (Set.Icc 0 1)))
    (hh : MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume.restrict (Set.Icc 0 1)) := by pw_aesm) : MeasureTheory.eLpNorm h (ENNReal.ofReal r) (MeasureTheory.volume.restrict (Set.Icc 0 1)) = ENNReal.ofReal ((MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc 0 1)) (fun θ : ℝ => ‖h θ‖ ^ r)) ^ (1 / r)) := by
  have hne0 : (ENNReal.ofReal r : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hr
  have hnetop : (ENNReal.ofReal r : ℝ≥0∞) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hh) hne0 hnetop]
  rw [ENNReal.toReal_ofReal hr.le]
  have hnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 1)), 0 ≤ ‖h θ‖ ^ r :=
    ae_of_all _ fun θ => Real.rpow_nonneg (norm_nonneg _) r
  have hpow : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 1)),
      ‖h θ‖ₑ ^ r = ENNReal.ofReal (‖h θ‖ ^ r) :=
    ae_of_all _ fun θ => by
      rw [← ofReal_norm (h θ), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
  have hlin : ∫⁻ θ, ‖h θ‖ₑ ^ r ∂(MeasureTheory.volume.restrict (Set.Icc 0 1))
      = ENNReal.ofReal (∫ θ, ‖h θ‖ ^ r ∂(MeasureTheory.volume.restrict (Set.Icc 0 1))) := by
    rw [lintegral_congr_ae hpow]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  rw [hlin, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg_of_ae hnn) (by positivity)]

end Work.A3
