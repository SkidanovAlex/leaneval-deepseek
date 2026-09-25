import Mathlib
import Submission.Work.NN.Core.PertL2Defs

open MeasureTheory Set

namespace Work.NN.Core

/-- For `g : ℂⁿ → ℂ` in `L²(wMeas n φ)`, the square of the `L²`-norm of its class is the
weighted integral `wnSq0 φ g = ∫ ‖g z‖² e^{-φ z}`.  This is the `Lp`-side identification of the
weighted `(0,0)`-norm used in the `L²_φ` calculus. -/
theorem norm_sq_toLp_wMeas {n : ℕ} {φ : Work.NN.Assemble.Cn n → ℝ} (hφ : Measurable φ)
    {g : Work.NN.Assemble.Cn n → ℂ} (hg : MeasureTheory.MemLp g 2 (Work.NN.Core.wMeas n φ)) :
    ‖MeasureTheory.MemLp.toLp g hg‖ ^ 2 = Work.NN.Assemble.wnSq0 φ g := by
  -- The `L²`-norm is `(∫ ‖g z‖² ∂(wMeas n φ))^(1/2)`.
  have hnorm : ‖MeasureTheory.MemLp.toLp g hg‖
      = (∫ z, ‖g z‖ ^ (2 : ℝ) ∂(Work.NN.Core.wMeas n φ)) ^ ((2 : ℝ)⁻¹) := by
    rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.toReal_eLpNorm]
    exact MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hg.aestronglyMeasurable
  rw [hnorm]
  -- Squaring the square root.
  rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) from by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · -- `‖g z‖ ^ (2 : ℝ) = ‖g z‖ ^ 2`.
    have hI : (∫ z, ‖g z‖ ^ (2 : ℝ) ∂(Work.NN.Core.wMeas n φ))
        = ∫ z, ‖g z‖ ^ 2 ∂(Work.NN.Core.wMeas n φ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Real.rpow_two]
    rw [hI]
    -- Change of measure: `∫ F ∂(volume.withDensity ρ) = ∫ ρ · F ∂volume`.
    have hf : Measurable (fun z : Work.NN.Assemble.Cn n => ENNReal.ofReal (Real.exp (-(φ z)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hφ.neg)
    have hchange : (∫ z, ‖g z‖ ^ 2 ∂(Work.NN.Core.wMeas n φ))
        = ∫ z, (ENNReal.ofReal (Real.exp (-(φ z)))).toReal * ‖g z‖ ^ 2 ∂volume := by
      rw [show Work.NN.Core.wMeas n φ
            = volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-(φ z)))) from rfl]
      exact integral_withDensity_eq_integral_toReal_smul (μ := volume) hf
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun z => ‖g z‖ ^ 2)
    rw [hchange]
    rw [show (fun z => (ENNReal.ofReal (Real.exp (-(φ z)))).toReal * ‖g z‖ ^ 2)
        = (fun z => ‖g z‖ ^ 2 * Real.exp (-(φ z))) from by
      funext z
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      ring]
    rfl
  · exact integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _

end Work.NN.Core
