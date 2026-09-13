import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_affine_apply

namespace Commons.Analysis.Calculus.FDeriv

/-- Second-derivative chain rule for the affine reparametrisation `y ↦ r⁻¹ • (y - x₀)`.
If `χ` is `C²` at `r⁻¹ • (x - x₀)`, then the second derivative of
`y ↦ χ (r⁻¹ • (y - x₀))` at `x` is `r⁻¹ * r⁻¹` times the second derivative of `χ`
at `r⁻¹ • (x - x₀)`. -/
theorem fderiv_fderiv_comp_affine_sub_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : E → ℝ} {r : ℝ} (hr : r ≠ 0) {x₀ x : E} (hχ : ContDiffAt ℝ 2 χ (r⁻¹ • (x - x₀))) : fderiv ℝ (fderiv ℝ (fun y : E => χ (r⁻¹ • (y - x₀)))) x = (r⁻¹ * r⁻¹) • fderiv ℝ (fderiv ℝ χ) (r⁻¹ • (x - x₀)) := by
  -- Rewrite `r⁻¹ • (x - x₀)` as the affine expression `r⁻¹ • x + -(r⁻¹ • x₀)`.
  have harg : r⁻¹ • x + -(r⁻¹ • x₀) = r⁻¹ • (x - x₀) := by rw [smul_sub]; abel
  have hχ' : ContDiffAt ℝ 2 χ (r⁻¹ • x + -(r⁻¹ • x₀)) := by
    rw [harg]; exact hχ
  -- Pointwise identity for the second iterated derivatives, from the affine chain rule.
  have key : ∀ m : Fin 2 → E,
      (iteratedFDeriv ℝ 2 (fun y : E => χ (r⁻¹ • (y - x₀))) x) m
        = (r⁻¹ * r⁻¹) * (iteratedFDeriv ℝ 2 χ (r⁻¹ • (x - x₀))) m := by
    intro m
    have h := iteratedFDeriv_two_affine_apply (u := χ) (y := -(r⁻¹ • x₀)) (x := x)
      (a := 1) (b := r⁻¹) hχ' m
    have hfun : (fun z : E => 1 * χ (r⁻¹ • z + -(r⁻¹ • x₀)))
        = (fun y : E => χ (r⁻¹ • (y - x₀))) := by
      funext z; rw [one_mul, smul_sub, sub_eq_add_neg]
    rw [hfun] at h
    rw [h, harg]
    ring
  -- Convert the second derivatives to iterated derivatives and conclude pointwise.
  ext u v
  rw [smul_apply, smul_apply, smul_eq_mul]
  have h1 : (iteratedFDeriv ℝ 2 (fun y : E => χ (r⁻¹ • (y - x₀))) x) ![u, v]
      = (fderiv ℝ (fderiv ℝ (fun y : E => χ (r⁻¹ • (y - x₀)))) x) u v := by
    simpa using iteratedFDeriv_two_apply (𝕜 := ℝ)
      (f := fun y : E => χ (r⁻¹ • (y - x₀))) x ![u, v]
  have h2 : (iteratedFDeriv ℝ 2 χ (r⁻¹ • (x - x₀))) ![u, v]
      = (fderiv ℝ (fderiv ℝ χ) (r⁻¹ • (x - x₀))) u v := by
    simpa using iteratedFDeriv_two_apply (𝕜 := ℝ)
      (f := χ) (z := r⁻¹ • (x - x₀)) ![u, v]
  rw [← h1, ← h2]
  exact key ![u, v]

end Commons.Analysis.Calculus.FDeriv
