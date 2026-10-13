import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
The generic domination step: if the angular integrand `K θ * |Y s θ|` is dominated by
`A * cos θ` on `Iθ = [0,π/2]`, then the density `L12dens K Y s = ∫ θ in Iθ, K θ * Y s θ / s`
is bounded by `A / s`.  Uses `norm_integral_le_integral_norm`, `abs_mul`, `abs_div`,
`abs_of_nonneg (K ≥ 0 on Iθ)`, `MeasureTheory.integral_mono_of_nonneg` against the
integrable majorant `A * cos θ` (continuous on the compact interval) and
`∫ θ in Iθ, Real.cos θ = 1` (interval integral: `∫_0^{π/2} cos = 1`).
-/
/-! ## Elementary angular facts used below -/

/-- `K θ = 3 sin θ cos²θ` is nonnegative on `Iθ = [0,π/2]`. -/
lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (sq_nonneg _)

/-- The normalisation `∫_0^{π/2} cos θ dθ = 1`. -/
lemma integral_cos_Iθ : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos])]
  rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero]
  norm_num

theorem AbsL12densLe {Y : ℝ → ℝ → ℝ} {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (h : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |Y s θ| ≤ A * Real.cos θ) :
    |Work.FM.L12dens Work.Spaces.K Y s| ≤ A / s := by
  have _hA : 0 ≤ A := hA
  -- `L12dens K Y s` is the set integral of `K θ * Y s θ / s` over `Iθ = [0,π/2]`.
  have hmono : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s := by
    refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => abs_nonneg _) ?_ ?_
    · intro θ hθ
      rw [abs_div, abs_mul, abs_of_nonneg (K_nonneg_of_mem_Iθ hθ), abs_of_pos hs]
      exact div_le_div_of_nonneg_right (h θ hθ) hs.le
    · rw [Work.Spaces.Iθ]
      exact (continuous_const.mul Real.continuous_cos).div_const s |>.integrableOn_Icc
  have h2 : (∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s)
      = A / s * (∫ θ in Work.Spaces.Iθ, Real.cos θ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc |Work.FM.L12dens Work.Spaces.K Y s|
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y s θ / s| := by
        show |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ / s| ≤ _
        exact MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s := hmono
    _ = A / s * (∫ θ in Work.Spaces.Iθ, Real.cos θ) := h2
    _ = A / s := by rw [integral_cos_Iθ, mul_one]

end Work.FTS.StrongEps.E5Aux2
