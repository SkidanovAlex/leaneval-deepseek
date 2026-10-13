import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Scaling.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

open Set

/-- The scaling `(x,t) ↦ (λx, λ²t)` maps the unit time strip into the strip of height `T = λ²`. -/
theorem mapsTo_rescale {lam T : ℝ} (hlam : lam ≠ 0) (hsq : lam ^ 2 = T) :
    MapsTo (fun z : Work.SolutionDelivery.R3 × ℝ => (lam • z.1, lam ^ 2 * z.2))
      (Set.univ ×ˢ Set.Ico 0 1) (Set.univ ×ˢ Set.Ico 0 T) := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ico] at ht ⊢
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (le_of_lt (sq_pos_of_ne_zero hlam)) ht.1
  · rw [← hsq]
    exact mul_lt_of_lt_one_right (sq_pos_of_ne_zero hlam) ht.2

/-- **The rescaling `x ↦ λ • u (λ • x) (λ² t)` preserves `C¹` regularity** on the unit time strip,
from `C¹` regularity of `u` on the strip of height `T = λ²` (with `λ ≠ 0`).

The rescaled field is the composition of `u.uncurry` with the affine scaling `(x,t) ↦ (λx, λ²t)`
followed by the scalar multiplication by `λ`, and the scaling carries `ℝ³ × [0,1)` into
`ℝ³ × [0,T)`. -/
theorem contDiffOn_rescale {lam T : ℝ} {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    (hlam : lam ≠ 0) (hsq : lam ^ 2 = T)
    (h : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ico 0 T)) :
    ContDiffOn ℝ 1 (Work.SolutionDelivery.rescale lam u).uncurry (Set.univ ×ˢ Set.Ico 0 1) := by
  have hφcont : ContDiff ℝ 1
      (fun z : Work.SolutionDelivery.R3 × ℝ => (lam • z.1, lam ^ 2 * z.2)) := by
    fun_prop
  have hcomp : ContDiffOn ℝ 1
      (u.uncurry ∘ (fun z : Work.SolutionDelivery.R3 × ℝ => (lam • z.1, lam ^ 2 * z.2)))
      (Set.univ ×ˢ Set.Ico 0 1) :=
    h.comp hφcont.contDiffOn (mapsTo_rescale hlam hsq)
  have hsmul : ContDiffOn ℝ 1
      (fun z => lam •
        (u.uncurry ∘ (fun z : Work.SolutionDelivery.R3 × ℝ => (lam • z.1, lam ^ 2 * z.2))) z)
      (Set.univ ×ˢ Set.Ico 0 1) := hcomp.const_smul lam
  refine hsmul.congr ?_
  intro z hz
  rfl

end Work.SolutionDelivery.Scaling
