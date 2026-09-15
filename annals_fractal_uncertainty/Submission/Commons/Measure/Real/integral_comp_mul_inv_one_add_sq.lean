import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Measure.Real

open MeasureTheory

/-- **Scaling of an integral against the Poisson weight.**  For `σ > 0` and any `g : ℝ → ℝ`,
substituting `u = tσ` turns the integral `∫ t, g (tσ) (1+t²)⁻¹` into a Poisson-kernel integral
`σ ∫ u, g u (σ² + u²)⁻¹`. -/
theorem integral_comp_mul_inv_one_add_sq {g : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.integral MeasureTheory.volume (fun t : ℝ => g (t * σ) * (1 + t ^ 2)⁻¹)
      = σ * MeasureTheory.integral MeasureTheory.volume (fun u : ℝ => g u * (σ ^ 2 + u ^ 2)⁻¹) := by
  have hσ' : σ ≠ 0 := hσ.ne'
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ'
  -- The change-of-variables integrand: `H u = g u * σ² * (σ² + u²)⁻¹`.
  let H : ℝ → ℝ := fun u => g u * (σ ^ 2 * (σ ^ 2 + u ^ 2)⁻¹)
  have hH : ∀ u, H u = σ ^ 2 * (g u * (σ ^ 2 + u ^ 2)⁻¹) := by
    intro u; simp only [H]; ring
  -- Pointwise identity of the two integrands under `u = t σ`.
  have hpt : ∀ t : ℝ, g (t * σ) * (1 + t ^ 2)⁻¹ = H (t * σ) := by
    intro t
    have key : σ ^ 2 * (σ ^ 2 + (t * σ) ^ 2)⁻¹ = (1 + t ^ 2)⁻¹ := by
      rw [show σ ^ 2 + (t * σ) ^ 2 = σ ^ 2 * (1 + t ^ 2) by ring, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ hσ2, one_mul]
    simp only [H]
    rw [key]
  -- Pull the constant `σ²` out of the integral of `H`.
  have hInt : MeasureTheory.integral MeasureTheory.volume H
      = σ ^ 2 * MeasureTheory.integral MeasureTheory.volume
          (fun u : ℝ => g u * (σ ^ 2 + u ^ 2)⁻¹) := by
    have h1 : MeasureTheory.integral MeasureTheory.volume H
        = MeasureTheory.integral MeasureTheory.volume
            (fun u : ℝ => σ ^ 2 * (g u * (σ ^ 2 + u ^ 2)⁻¹)) := by
      apply integral_congr_ae
      filter_upwards with u
      exact hH u
    rw [h1, integral_const_mul]
  calc MeasureTheory.integral MeasureTheory.volume (fun t : ℝ => g (t * σ) * (1 + t ^ 2)⁻¹)
      = MeasureTheory.integral MeasureTheory.volume (fun t : ℝ => H (t * σ)) := by
        apply integral_congr_ae
        filter_upwards with t
        exact hpt t
    _ = |σ⁻¹| • MeasureTheory.integral MeasureTheory.volume H :=
        Measure.integral_comp_mul_right H σ
    _ = σ⁻¹ * MeasureTheory.integral MeasureTheory.volume H := by
        rw [abs_of_pos (inv_pos.mpr hσ), smul_eq_mul]
    _ = σ⁻¹ * (σ ^ 2 * MeasureTheory.integral MeasureTheory.volume
          (fun u : ℝ => g u * (σ ^ 2 + u ^ 2)⁻¹)) := by
        rw [hInt]
    _ = σ * MeasureTheory.integral MeasureTheory.volume
          (fun u : ℝ => g u * (σ ^ 2 + u ^ 2)⁻¹) := by
        rw [← mul_assoc, show σ⁻¹ * σ ^ 2 = σ by field_simp]

end Commons.Measure.Real