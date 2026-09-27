import Mathlib
import Submission.Work.Whitney.CutPush.exists_fderiv_close_of_contDiff

/-!
# The mean-value bound on the support (germ recipe, step (b))

Step (b) of the germ-extension recipe (`NOTES_hasFingerData_S33.md` §6, §10, §11): a `C^∞` map whose
derivative has norm `≤ ε` on the ball of radius `ρ` around `0` is `ε`-Lipschitz there.  This is the
mean value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le` applied to the convex ball
`Metric.ball 0 ρ`.

Together with step (a) (`Work.Whitney.CutPush.exists_fderiv_close_of_contDiff`, which produces the
bound `‖fderiv ℝ W y‖ ≤ ε` on the ball for the first-order remainder `W := Φ - Φ 0 - Ae ·`) this
gives the two estimates the assembly (c) consumes for the interpolated perturbation
`V := Ae⁻¹ ∘ (χ • W)`:

* `‖W x - W y‖ ≤ ε ‖x - y‖` (this file), and
* `‖W y‖ ≤ ε ‖y‖` (the same bound with `x = 0`, using `W 0 = 0`).
-/

open scoped ContDiff

namespace Work.Whitney.CutPush

/-- **The mean value bound.**  If `‖fderiv ℝ W‖ ≤ ε` on the ball of radius `ρ`, then `W` is
`ε`-Lipschitz there. -/
theorem norm_sub_le_of_fderiv_close {N : ℕ}
    (W : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (ε ρ : ℝ) (hρ : 0 < ρ)
    (hclose : ∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < ρ → ‖fderiv ℝ W y‖ ≤ ε) :
    ∀ x y : EuclideanSpace ℝ (Fin N), ‖x‖ < ρ → ‖y‖ < ρ →
      ‖W x - W y‖ ≤ ε * ‖x - y‖ := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  intro x y hx hy
  have hdiffW : Differentiable ℝ W := hW.differentiable hne
  have hdiff : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ,
      DifferentiableAt ℝ W z :=
    fun z _ => hdiffW.differentiableAt
  have hbound : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ,
      ‖fderiv ℝ W z‖ ≤ ε := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hclose z hz
  have hxm : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ := by
    rwa [Metric.mem_ball, dist_zero_right]
  have hym : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ := by
    rwa [Metric.mem_ball, dist_zero_right]
  have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (f := W) (C := ε)
    (s := Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ) hdiff hbound (convex_ball _ _) hxm hym
  simpa [norm_sub_rev] using h1

end Work.Whitney.CutPush
