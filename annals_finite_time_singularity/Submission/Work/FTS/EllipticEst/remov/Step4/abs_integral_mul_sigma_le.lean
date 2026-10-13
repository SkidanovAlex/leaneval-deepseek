import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Step4

open MeasureTheory

/-! ## A weighted Cauchy–Schwarz (Young) bound on the angular interval

This file proves the elementary "absorbing" inequality used in step 4 of the
elliptic estimates: for a *non-negative* angular weight `σ`, if `f²σ` and `h²σ`
are integrable on `Iθ = [0, π/2]` then `f·h·σ` is integrable there and

  `|∫ f h σ| ≤ ε ∫ f²σ + (1/(4ε)) ∫ h²σ`.

The pointwise input is Young's inequality `2ab ≤ a² + b²` applied to
`a = √ε |f| √σ`, `b = |h| √σ/(2√ε)`; the specific weight of the paper is
`σ θ = sin(2θ)^{2-γ}` (with `2 - γ > 0` for the relevant range of `γ`). -/

/-- Young's inequality in the form needed below: for `ε > 0`,
`|x*y| ≤ ε x² + (1/(4ε)) y²`.  (The constant `4` is the sharp one: it is
`(2√ε)²` from `2ab ≤ a² + b²` with `a = √ε x`, `b = y/√ε`.) -/
theorem abs_mul_le_eps_sq_add (ε : ℝ) (hε : 0 < ε) (x y : ℝ) :
    |x * y| ≤ ε * x ^ 2 + (1 / (4 * ε)) * y ^ 2 := by
  have h4 : (0 : ℝ) < 4 * ε := by positivity
  have key : 4 * ε * |x * y| ≤ 4 * ε ^ 2 * x ^ 2 + y ^ 2 := by
    have h5 := sq_nonneg (2 * ε * |x| - |y|)
    rw [abs_mul]
    nlinarith [sq_abs x, sq_abs y]
  have h6 : |x * y| ≤ (4 * ε ^ 2 * x ^ 2 + y ^ 2) / (4 * ε) := by
    rw [le_div_iff₀ h4]
    linarith [key]
  have h7 : (4 * ε ^ 2 * x ^ 2 + y ^ 2) / (4 * ε) = ε * x ^ 2 + (1 / (4 * ε)) * y ^ 2 := by
    field_simp
  linarith [h6, h7]

/-- Weighted Cauchy–Schwarz ("absorbing") inequality on the angular interval
`Iθ = [0,π/2]`: for a non-negative weight `σ`, if `f²σ` and `h²σ` are integrable
then so is `f·h·σ`, and the integral is bounded by
`ε ∫ f²σ + (1/(4ε)) ∫ h²σ`. -/
theorem integrableOn_mul_of_sq_integrableOn (ε : ℝ) (hε : 0 < ε) {σ f h : ℝ → ℝ}
    (hσm : AEStronglyMeasurable σ (volume.restrict Work.Spaces.Iθ))
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hfm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (hhm : AEStronglyMeasurable h (volume.restrict Work.Spaces.Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hh : IntegrableOn (fun θ => (h θ) ^ 2 * σ θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => f θ * h θ * σ θ) Work.Spaces.Iθ
      ∧ |∫ θ in Work.Spaces.Iθ, f θ * h θ * σ θ|
          ≤ ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
            + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := isClosed_Icc.measurableSet
  -- pointwise Young bound
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, |f θ * h θ * σ θ| ≤
      ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ) := by
    intro θ hθ
    have hσ0 : 0 ≤ σ θ := hσnn θ hθ
    have h1 : |f θ * h θ * σ θ| = |f θ * h θ| * σ θ := by
      rw [abs_mul, abs_of_nonneg hσ0]
    have h3 := mul_le_mul_of_nonneg_right (abs_mul_le_eps_sq_add ε hε (f θ) (h θ)) hσ0
    rw [h1]
    calc |f θ * h θ| * σ θ
        ≤ (ε * (f θ) ^ 2 + (1 / (4 * ε)) * (h θ) ^ 2) * σ θ := h3
      _ = ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ) := by ring
  -- the dominating function is integrable
  have hGint : IntegrableOn
      (fun θ => ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ))
      Work.Spaces.Iθ :=
    (hf.const_mul ε).add (hh.const_mul (1 / (4 * ε)))
  have hgm : AEStronglyMeasurable (fun θ => f θ * h θ * σ θ)
      (volume.restrict Work.Spaces.Iθ) := (hfm.mul hhm).mul hσm
  have hmain : IntegrableOn (fun θ => f θ * h θ * σ θ) Work.Spaces.Iθ := by
    refine Integrable.mono' hGint hgm ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    simpa [Real.norm_eq_abs] using hpt θ hθ
  refine ⟨hmain, ?_⟩
  -- comparison of integrals
  have hmono : ∫ θ in Work.Spaces.Iθ, |f θ * h θ * σ θ|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ)) :=
    setIntegral_mono_ae_restrict hmain.abs hGint (by
      filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact hpt θ hθ)
  have hsplit : ∫ θ in Work.Spaces.Iθ,
        (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ))
      = ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
        + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := by
    rw [integral_add (hf.const_mul ε) (hh.const_mul (1 / (4 * ε))),
      integral_const_mul, integral_const_mul]
  calc |∫ θ in Work.Spaces.Iθ, f θ * h θ * σ θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |f θ * h θ * σ θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ)) := hmono
    _ = ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
        + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := hsplit

/-- The weight `σ θ = sin(2θ)^{2-γ}` of the elliptic estimates is measurable. -/
theorem measurable_sin_two_rpow (γ : ℝ) :
    Measurable fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  measurability

theorem abs_integral_mul_sigma_le (γ ε : ℝ) (hε : 0 < ε) {f h : ℝ → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hhm : MeasureTheory.AEStronglyMeasurable h
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => (h θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => f θ * h θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ |∫ θ in Work.Spaces.Iθ, f θ * h θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)|
          ≤ ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  have hσm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (measurable_sin_two_rpow γ).aestronglyMeasurable
  exact integrableOn_mul_of_sq_integrableOn ε hε hσm hσnn hfm hhm hf hh

end Work.FTS.EllipticEst.remov.Step4
