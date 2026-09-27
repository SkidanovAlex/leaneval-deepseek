import Mathlib
import Submission.Work.Whitney.EuclidModel

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **Agreement of the transported scaled model with the axis outside the ball.**  If `β` agrees
with `inclModel` outside the sup ball of radius `R` on `(Fin n → ℝ)`, then `euclidModel n lam β`
agrees with the axis outside the `L²` ball of radius `R` on `EuclideanSpace ℝ (Fin n)`: the scaling
`lam ≥ √n` shrinks the region where the model is active into the `L²` ball. -/
theorem euclidModel_eq_axis {n : ℕ} {lam R : ℝ}
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hlam : 0 < lam) (hsqrt : Real.sqrt n ≤ lam) (hR : 0 < R)
    (hβR : ∀ x, R ≤ ‖x‖ → β x = Work.Whitney.inclModel n x)
    {u : EuclideanSpace ℝ (Fin n)} (hu : R ≤ ‖u‖) :
    Work.Whitney.euclidModel n lam β u = (u, 0) := by
  -- Step 1: the sup norm of `lam • u.ofLp` is at least `R`.
  -- `‖u‖ ≤ √n * ‖u.ofLp‖` (the `L²`/sup norm comparison) and `√n ≤ lam`, so
  -- `R ≤ ‖u‖ ≤ √n ‖u.ofLp‖ ≤ lam ‖u.ofLp‖ = ‖lam • u.ofLp‖`.
  have h1 : R ≤ Real.sqrt n * ‖euclidOfLp n u‖ := by
    have h : ‖u‖ = ‖lpOfEuclid n (euclidOfLp n u)‖ := by simp
    rw [h] at hu
    exact hu.trans (norm_lpOfEuclid_le n (euclidOfLp n u))
  have h2 : Real.sqrt n * ‖euclidOfLp n u‖ ≤ lam * ‖euclidOfLp n u‖ :=
    mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
  have h3 : lam * ‖euclidOfLp n u‖ = ‖lam • euclidOfLp n u‖ := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hlam)]
  have hx : R ≤ ‖lam • euclidOfLp n u‖ := by rw [← h3]; exact h1.trans h2
  -- Step 2: `β` agrees with the linear inclusion there.
  have hβ : β (lam • euclidOfLp n u) = inclModel n (lam • euclidOfLp n u) := hβR _ hx
  -- Step 3: undo the scaling, giving the inclusion `x ↦ (x, 0)` in the sup-norm world.
  have hsm : scaledModel n lam β (euclidOfLp n u) = (euclidOfLp n u, 0) := by
    rw [scaledModel_apply, hβ, inclModel]
    ext <;> simp [smul_smul, inv_mul_cancel₀ hlam.ne']
  -- Step 4: transport back through `pairToE`, which is the identity on the source point.
  rw [euclidModel_apply, hsm]
  simp

end Work.Whitney
