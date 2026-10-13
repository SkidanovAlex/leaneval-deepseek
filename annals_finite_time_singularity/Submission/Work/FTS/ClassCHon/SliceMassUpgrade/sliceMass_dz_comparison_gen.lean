import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped ENNReal Real

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The same comparison as `sliceMass_dz_comparison`, with an arbitrary weight `τ`
in place of `sEta`.  The only property of the weight that is used is that it is the
*same* function in both integrands: the right-hand integrand is `s²` times the
left-hand one, and `(z₁²)⁻¹ · s² ≥ 1` since `0 < z₁ ≤ s`. -/
theorem sliceMass_dz_comparison_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ} {z₁ s : ℝ}
    (hz₁ : 0 < z₁) (hz₁s : z₁ ≤ s) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
        * ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2) := by
  set A : ENNReal := ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) with hA
  have hInt : (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
      = ENNReal.ofReal (s ^ 2) * A := by
    rw [show (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
        = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) from
        MeasureTheory.lintegral_congr (fun θ => by
          rw [show τ θ * (s * Work.Spaces.pz F s θ) ^ 2
              = s ^ 2 * (τ θ * (Work.Spaces.pz F s θ) ^ 2) from by ring]
          exact ENNReal.ofReal_mul (by positivity))]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hInt, ← mul_assoc]
  have h1 : (1 : ENNReal) ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹ * ENNReal.ofReal (s ^ 2) := by
    have hz1sq_pos : (0 : ℝ) < z₁ ^ 2 := by positivity
    have hsge : z₁ ^ 2 ≤ s ^ 2 := by nlinarith
    have hreal : (1 : ℝ) ≤ (z₁ ^ 2)⁻¹ * s ^ 2 := by
      calc (1 : ℝ) = (z₁ ^ 2)⁻¹ * z₁ ^ 2 := (inv_mul_cancel₀ (by positivity : z₁ ^ 2 ≠ 0)).symm
        _ ≤ (z₁ ^ 2)⁻¹ * s ^ 2 := mul_le_mul_of_nonneg_left hsge (by positivity)
    rw [← ENNReal.ofReal_inv_of_pos hz1sq_pos]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (z₁ ^ 2)⁻¹)]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hreal
  exact le_mul_of_one_le_left' h1

end Work.FTS.ClassCHon.SliceMassUpgrade
