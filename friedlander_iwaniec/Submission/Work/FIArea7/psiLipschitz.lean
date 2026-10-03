import Mathlib

namespace Work.FIArea7

/-- A `C¹` function whose derivative is bounded by `K` is `K`-Lipschitz on `ℝ`. -/
theorem psiLipschitz {P : ℝ → ℝ} {K : ℝ} (hP : ContDiff ℝ 1 P)
    (hK : ∀ u : ℝ, |deriv P u| ≤ K) (u v : ℝ) : |P u - P v| ≤ K * |u - v| := by
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ P x :=
    fun x _ => hP.differentiable_one.differentiableAt
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv P x‖ ≤ K := by
    intro x _; simpa using hK x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := P) (s := Set.univ) (x := v) (y := u)
    hdiff hbound convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa using h

end Work.FIArea7
