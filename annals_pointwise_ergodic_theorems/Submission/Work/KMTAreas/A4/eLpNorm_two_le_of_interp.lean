import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- **Log-convexity (Lyapunov) interpolation of the `ℓᵖ` norm on `ℤ`.**

If `1/2 = (1-θ)/p + θ/q` with `0 < θ < 1` and `‖w‖_{ℓᵖ} ≤ M₁`, `‖w‖_{ℓᵍ} ≤ M₂`, then
`‖w‖_{ℓ²} ≤ M₁^{1-θ} M₂^θ`.  This is the standard Hölder interpolation of `Lᵖ` seminorms
(`Interp.eLpNorm_interp`) followed by monotonicity of `x ↦ x ^ t` and `ofReal` arithmetic;
measurability is free because the counting measure on `ℤ` lives on the discrete σ-algebra. -/
theorem eLpNorm_two_le_of_interp {w : ℤ → ℂ} {p q θ : ℝ} (hp : 1 < p) (hq : 1 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hrel : 1 / 2 = (1 - θ) / p + θ / q) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h₁ : MeasureTheory.eLpNorm w (ENNReal.ofReal p) MeasureTheory.Measure.count ≤ ENNReal.ofReal M₁) (h₂ : MeasureTheory.eLpNorm w (ENNReal.ofReal q) MeasureTheory.Measure.count ≤ ENNReal.ofReal M₂) : MeasureTheory.eLpNorm w 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal (M₁ ^ (1 - θ) * M₂ ^ θ) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hw : AEMeasurable w Measure.count := (measurable_of_countable w).aemeasurable
  have hkey := Interp.eLpNorm_interp (μ := Measure.count) (f := w) hp0 hq0 h2 hθ0 hθ1 hrel hw
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
  refine hkey.trans ?_
  have h1' : eLpNorm w (ENNReal.ofReal p) Measure.count ^ (1 - θ) ≤
      (ENNReal.ofReal M₁) ^ (1 - θ) :=
    ENNReal.rpow_le_rpow h₁ (by linarith)
  have h2' : eLpNorm w (ENNReal.ofReal q) Measure.count ^ θ ≤ (ENNReal.ofReal M₂) ^ θ :=
    ENNReal.rpow_le_rpow h₂ hθ0.le
  have heq : ENNReal.ofReal (M₁ ^ (1 - θ) * M₂ ^ θ)
      = (ENNReal.ofReal M₁) ^ (1 - θ) * (ENNReal.ofReal M₂) ^ θ := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM₁ (1 - θ)),
      ← ENNReal.ofReal_rpow_of_nonneg hM₁ (by linarith : (0 : ℝ) ≤ 1 - θ),
      ← ENNReal.ofReal_rpow_of_nonneg hM₂ hθ0.le]
  exact (mul_le_mul' h1' h2').trans (le_of_eq heq.symm)

end Work.KMTAreas.A4
