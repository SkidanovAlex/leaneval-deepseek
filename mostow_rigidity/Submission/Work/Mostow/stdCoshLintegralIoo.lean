import Mathlib
import Submission.Work.Mostow.stdFermiDefs

open MeasureTheory

namespace Work.Mostow

open scoped ENNReal

/-- For `ρ > 0`, the Lebesgue integral (as an `ℝ≥0∞`-valued integral of the nonnegative
real function `r ↦ cosh r`) over the interval `(-ρ, ρ)` equals `2 * sinh ρ`. -/
theorem stdCoshLintegralIoo (ρ : ℝ) (hρ : 0 < ρ) :
    ∫⁻ r in Set.Ioo (-ρ) ρ, ENNReal.ofReal (Real.cosh r) = ENNReal.ofReal (2 * Real.sinh ρ) := by
  have hle : -ρ ≤ ρ := by linarith
  -- `cosh` is integrable on the interval and nonnegative there.
  have hint : IntegrableOn Real.cosh (Set.Ioo (-ρ) ρ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp
      (Real.continuous_cosh.intervalIntegrable _ _)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-ρ) ρ)] Real.cosh :=
    Filter.Eventually.of_forall fun x => (Real.cosh_pos x).le
  -- Convert the `ℝ≥0∞`-valued integral into `ofReal` of the Bochner integral.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Ioo (-ρ) ρ)) hint hnn]
  congr 1
  -- Evaluate the Bochner integral of `cosh`.
  have h1 : (∫ x in Set.Ioo (-ρ) ρ, Real.cosh x) = ∫ x in (-ρ)..ρ, Real.cosh x := by
    rw [show (∫ x in Set.Ioo (-ρ) ρ, Real.cosh x)
          = ∫ x, Real.cosh x ∂(volume.restrict (Set.Ioo (-ρ) ρ)) from rfl,
        MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegral.integral_of_le hle).symm
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sinh x) (Real.continuous_cosh.intervalIntegrable _ _)]
  rw [Real.sinh_neg]
  ring

end Work.Mostow
