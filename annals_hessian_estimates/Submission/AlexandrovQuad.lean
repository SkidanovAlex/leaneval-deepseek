/-
The quadratic form associated with a matrix `M x₀` and the rewriting of the second order Taylor
remainder `Submission.taylorRemainder` in terms of a continuous linear form and a continuous
bilinear form.  These are the algebraic ingredients of the pointwise slope estimate `(point)` in
the proof of Proposition 3.1 of Shankar--Yuan.
-/
import Mathlib
import Submission.WeakDerivative

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The continuous bilinear form with coefficient matrix `M · x₀`, i.e.
`Q a b = ∑ i, ∑ j, (M i j x₀ / 2) * a i * b j`. -/
noncomputable def quadM (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ :=
  ∑ i, ∑ j, (EuclideanSpace.proj i).smulRight ((M i j x₀ / 2) • (EuclideanSpace.proj j))

theorem quadM_apply (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ a b : ℝ⁴) :
    quadM M x₀ a b = ∑ i, ∑ j, (M i j x₀ / 2) * (a i) * (b j) := by
  simp only [quadM, sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    PiLp.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The second order Taylor remainder is the difference of `g` and the affine function minus the
quadratic form `quadM M x₀`. -/
theorem taylorRemainder_eq (g : ℝ⁴ → ℝ) (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ)
    (x₀ y : ℝ⁴) :
    taylorRemainder g G M x₀ y
      = g y - g x₀ - (innerSL ℝ (G x₀)) (y - x₀) - quadM M x₀ (y - x₀) (y - x₀) := by
  rw [taylorRemainder, quadM_apply]
  rw [← innerSL_apply_apply]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem taylorRemainder_self (g : ℝ⁴ → ℝ) (G : ℝ⁴ → ℝ⁴) (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ)
    (x₀ : ℝ⁴) : taylorRemainder g G M x₀ x₀ = 0 := by
  simp [taylorRemainder]

/-- The polarization identity for a bilinear form: `Q a a - Q b b = Q a (a-b) + Q (a-b) b`. -/
theorem quadM_sub_eq (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (x₀ a b : ℝ⁴) :
    quadM M x₀ a a - quadM M x₀ b b
      = quadM M x₀ a (a - b) + quadM M x₀ (a - b) b := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

end Submission
