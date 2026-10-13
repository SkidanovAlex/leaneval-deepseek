import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- For `z > 0` the radial weight dominates the sharp power `1 / z ^ 4`:
`w(z)² = (1+z)⁴ / z⁴ ≥ 1 / z⁴` because `1 + z ≥ 1`. -/
theorem one_div_pow_four_le_w_sq {z : ℝ} (hz : 0 < z) :
    1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h14 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ h1z
  have hwz : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  rw [hwz]; gcongr

/-- The constant `w(z)²` (independent of `θ`) factors out of the `θ`-integral:
this is the linearity of the Bochner integral against `MeasureTheory.integral_const_mul`,
and it holds unconditionally (no integrability of the `θ`-slice is needed). -/
theorem integral_w_sq_mul (g : ℝ → ℝ → ℝ) (e z : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-e))
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
  have hpt : (fun θ : ℝ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-e))
      = fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) := by
    funext θ; ring
  rw [hpt]
  exact MeasureTheory.integral_const_mul _ _

theorem slice_not_integrable_of_lower_bound (g : ℝ → ℝ → ℝ) (e : ℝ)
    (hlow : ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Set.Ioo 0 ε,
        c ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) :
    ¬ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) Work.Spaces.Iz := by
  obtain ⟨ε, hε, c, hc, hbound⟩ := hlow
  -- On `(0, ε)` the full integrand dominates `c / z ^ 4`.
  have hkey : ∀ z ∈ Set.Ioo (0 : ℝ) ε,
      c / z ^ 4 ≤ ∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
    intro z hz
    have hzpos : 0 < z := hz.1
    rw [integral_w_sq_mul]
    have hw : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := one_div_pow_four_le_w_sq hzpos
    have hS : c ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) :=
      hbound z hz
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc c / z ^ 4 = c * (1 / z ^ 4) := by ring
      _ ≤ c * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hw hc.le
      _ = (Work.Spaces.w z) ^ 2 * c := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) :=
          mul_le_mul_of_nonneg_left hS hw2
  -- The sharp `1 / z ^ 4` singularity at the origin forces non-integrability on `(0, ε)`.
  have hnot : ¬ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow hc hε (by norm_num) hkey
  intro hF
  exact hnot (hF.mono_set Set.Ioi_subset_Ici_self)

end Work.FTS.EllipticEst.remov
