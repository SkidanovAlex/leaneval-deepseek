import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- On `Iθ = [0, π/2]` the weight `sin(2x)^{-η}` dominates `1` pointwise (except at the two
endpoints, which are null): `sin(2x) ∈ (0,1]` for `x ∈ (0,π/2)` and `η ≥ 0`.

Consequently the weighted `L²` integral of `(∂ₓh)²` over the full angular interval dominates
the integral over any initial segment `(0,θ]`, `θ < π/2`. -/
theorem sqIntegral_le_weightedIntegral {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ)) :
    (∫ x in (0:ℝ)..θ, (deriv h x) ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
  have hθ0 : (0 : ℝ) ≤ θ := le_of_lt hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  -- `(0,θ] ⊆ Iθ = [0,π/2]`
  have hsub : Set.Ioc (0 : ℝ) θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2.trans hθ2⟩
  -- on `(0,θ]` the sine is positive, hence `sin(2x)^{-η} ≥ 1` because `sin(2x) ≤ 1` and `η ≥ 0`
  have hsinpos : ∀ x ∈ Set.Ioc (0 : ℝ) θ, 0 < Real.sin (2 * x) := by
    intro x hx
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1]
    · linarith [hx.2, hθ.2]
  have hw1 : ∀ x ∈ Set.Ioc (0 : ℝ) θ, 1 ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hsinpos x hx) (Real.sin_le_one _) (by
      have heta : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
      linarith)
  have hfg : ∀ x ∈ Set.Ioc (0 : ℝ) θ,
      (deriv h x) ^ 2 ≤ (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    have h1 := hw1 x hx
    nlinarith [sq_nonneg (deriv h x)]
  -- Step 1: monotonicity of the integral on `(0,θ]` (both sides integrable there).
  have step1 : ∫ x in Set.Ioc (0 : ℝ) θ, (deriv h x) ^ 2
      ≤ ∫ x in Set.Ioc (0 : ℝ) θ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.integral_mono_ae (μ := volume.restrict (Set.Ioc (0 : ℝ) θ)) hint2 ?_ ?_
    · exact hint.mono_set hsub
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact hfg x hx
  -- Step 2: enlarging the set `(0,θ] ↦ Iθ` for a nonnegative integrand.
  have step2 : ∫ x in Set.Ioc (0 : ℝ) θ,
        (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
      ≤ ∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.setIntegral_mono_set (μ := volume) hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc)] with x hx
      have hs : 0 ≤ Real.sin (2 * x) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith [hx.1]
        · linarith [hx.2]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
    · filter_upwards with x hx
      exact hsub hx
  rw [intervalIntegral.integral_of_le hθ0]
  exact le_trans step1 step2

end Work.FTS.H2.DivQ
