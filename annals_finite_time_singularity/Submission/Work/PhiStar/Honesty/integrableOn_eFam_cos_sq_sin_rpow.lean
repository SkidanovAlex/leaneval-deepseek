import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PhiStar.Honesty

/-- `eFam m = cos · gC (2m+1) (sin ·)` is continuous (a polynomial composed with `sin`,
multiplied by `cos`). -/
lemma continuous_eFam (m : ℕ) :
    Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- `sin (2θ)^{η}` is continuous on `Iθ = [0, π/2]` (the base `sin (2θ)` is nonnegative there
and the exponent `η = 99/100` is nonnegative). -/
lemma continuousOn_sin_two_rpow_eta :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem integrableOn_eFam_cos_sq_sin_rpow (m : ℕ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ
    ∧ 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
  -- The integrand is continuous on the compact set `Iθ`, hence integrable.
  have hcont : ContinuousOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
    (((continuous_eFam m).mul Real.continuous_cos).pow 2).continuousOn.mul
      continuousOn_sin_two_rpow_eta
  have hI : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  constructor
  · exact hcont.integrableOn_compact isCompact_Icc
  · -- the integrand is nonnegative on `Iθ`
    exact MeasureTheory.setIntegral_nonneg hI (fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))

end Work.PhiStar.Honesty
