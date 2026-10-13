import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **From the squared boundary estimate to a linear pointwise bound.**  If a.e. `z > 0` satisfies

  `(f z θ - lam z)^2 ≤ 100/(γ-1) * sin(2θ)^{γ-1} * Ibd α f z`   for all `θ ∈ (0,π/4)`

(with `γ = Work.Spaces.gam α`, `0 < α ≤ 1`, so that `γ - 1 > 0`), then a.e. `z > 0` satisfies

  `|f z θ - lam z| ≤ (100/(γ-1) * Ibd α f z + 1) / 2`   for all `θ ∈ (0,π/4)`.

Route: `|f z θ - lam z| = sqrt ((f z θ - lam z)^2) ≤ sqrt (A * sin(2θ)^{γ-1} * Ibd α f z) ≤
sqrt (A * Ibd α f z) ≤ (A * Ibd α f z + 1)/2` with `A := 100/(γ-1) ≥ 0`, using
`sin(2θ)^{γ-1} ≤ 1` for `θ ∈ (0,π/4)` (`Real.rpow_le_one`), `Real.sqrt_le_sqrt`,
`Real.sqrt_mul`, and the elementary inequality `2 * sqrt x ≤ x + 1` for `x ≥ 0`; also
`0 ≤ Ibd α f z` (`integral_nonneg` on the nonnegative integrand, or `Real.rpow_nonneg`).
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem HbdPointwiseLe {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      (f z θ - lam z)^2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * Ibd α f z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      |f z θ - lam z| ≤ (100 / (Work.Spaces.gam α - 1) * Ibd α f z + 1) / 2 := by
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  have hA : 0 ≤ 100 / (Work.Spaces.gam α - 1) := by positivity
  filter_upwards [hbd] with z hz θ hθ
  -- nonnegativity of the angular energy `Ibd α f z`
  have hIbd : 0 ≤ Ibd α f z := by
    apply setIntegral_nonneg measurableSet_Icc
    intro σ hσ
    have hsin : 0 ≤ Real.sin (2 * σ) := by
      apply Real.sin_nonneg_of_mem_Icc
      constructor <;> linarith [hσ.1, hσ.2, Real.pi_pos]
    exact mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
  -- the squared bound at `θ`
  have hsin2 : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hrpow : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1) ≤ 1 :=
    Real.rpow_le_one hsin2.le (Real.sin_le_one _) hgam1.le
  have hsq : (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * Ibd α f z := by
    calc (f z θ - lam z) ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
            * Ibd α f z := hz θ hθ
      _ ≤ 100 / (Work.Spaces.gam α - 1) * 1 * Ibd α f z := by
          apply mul_le_mul_of_nonneg_right _ hIbd
          exact mul_le_mul_of_nonneg_left hrpow hA
      _ = 100 / (Work.Spaces.gam α - 1) * Ibd α f z := by ring
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((f z θ - lam z) ^ 2)
      ≤ Real.sqrt (100 / (Work.Spaces.gam α - 1) * Ibd α f z) := Real.sqrt_le_sqrt hsq
    _ ≤ (100 / (Work.Spaces.gam α - 1) * Ibd α f z + 1) / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by nlinarith [mul_nonneg hA hIbd], ?_⟩
        nlinarith [sq_nonneg (100 / (Work.Spaces.gam α - 1) * Ibd α f z - 1)]

end Work.FTS.StrongEps.EpsLocalPStar
