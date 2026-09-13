/-
# The weighted (localised) interior gradient estimate

Continues `Submission/SmoothGradientCenter.lean`.  Two consequences of
`Submission.interior_gradient_bound_at`:

* `Submission.gradient_bound_weighted`: for a smooth solution on `ball c r`,
  `‖Du z‖ * (r - dist z c) ≤ C (1+M)^2` — the constant is the distance from `z` to the boundary.
  (Since the right side is a `∃ C, 0 < C ∧ ...`, this is the form used downstream.)
-/
import Mathlib
import Submission.SmoothGradientCenter

open HessianEstimates
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace Pointwise

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **The weighted (localised) form of the interior gradient estimate**: the constant in front of
`|Du(z)|` is the distance from `z` to the boundary of the ball. -/
theorem gradient_bound_weighted :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (c : ℝ⁴) (r M : ℝ), 0 < r → 0 < M →
      ContDiffOn ℝ 3 u (ball c r) → (∀ x ∈ ball c r, |u x| ≤ M) →
      (∀ x ∈ ball c r, σ₂ (H u (ball c r) x) = 1) →
      (∀ x ∈ ball c r, 0 < (Δ u) x) →
      ∀ z ∈ ball c r, ‖fderiv ℝ u z‖ * (r - dist z c) ≤ C * (1 + M) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := interior_gradient_bound_at
  refine ⟨C, hCpos, ?_⟩
  intro u c r M hr hM hu hub hσ2 hΔ z hz
  have hzlt : dist z c < r := by rwa [mem_ball] at hz
  have hρ : 0 < r - dist z c := by linarith
  have hsub : ball z (r - dist z c) ⊆ ball c r := by
    intro w hw
    rw [mem_ball] at hw ⊢
    calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
      _ < (r - dist z c) + dist z c := by linarith [hw]
      _ = r := by ring
  have hu' : ContDiffOn ℝ 3 u (ball z (r - dist z c)) := hu.mono hsub
  have hub' : ∀ x ∈ ball z (r - dist z c), |u x| ≤ M := fun x hx => hub x (hsub hx)
  have hσ2' : ∀ x ∈ ball z (r - dist z c), σ₂ (H u (ball z (r - dist z c)) x) = 1 := by
    intro x hx
    rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hx) (isOpen_ball.mem_nhds (hsub hx))]
    exact hσ2 x (hsub hx)
  have hΔ' : ∀ x ∈ ball z (r - dist z c), 0 < (Δ u) x := fun x hx => hΔ x (hsub hx)
  exact hC u z (r - dist z c) M hρ hM hu' hub' hσ2' hΔ'

end Submission
