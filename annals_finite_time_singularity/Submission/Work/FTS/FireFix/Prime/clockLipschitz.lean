import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **The self-similar clock `B` is Lipschitz on the fake-time strip `[0,S]`.**

`RegPkg'` makes `B` differentiable on `[0,S]` with bounded `deriv`; the mean value theorem on the
convex interval `[0,S]` then turns that bound into a global Lipschitz constant
`K = max b₂ 0`, where `b₂` bounds `deriv B`.  (The `max` with `0` is what makes `K` nonnegative
regardless of the sign of the supplied bound.) -/
theorem clockLipschitz {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |B τ - B τ'| ≤ K * |τ - τ'| := by
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max b₂ 0, le_max_right _ _, fun τ hτ τ' hτ' => ?_⟩
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) S, DifferentiableAt ℝ B x :=
    fun x hx => (h.hBdiff x hx).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) S, ‖deriv B x‖ ≤ max b₂ 0 := fun x hx => by
    rw [Real.norm_eq_abs]
    exact le_trans (hb₂ x hx) (le_max_left _ _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 S) hτ' hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  simpa [abs_sub_comm] using hmvt

end Work.FTS.FireFix.Prime
