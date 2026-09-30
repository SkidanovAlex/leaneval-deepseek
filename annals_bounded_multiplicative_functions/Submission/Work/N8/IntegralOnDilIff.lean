import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Evaluating the dilation `dil a γ = γ (a ·)` at `x` gives `γ.eval (a * x)`. -/
theorem eval_dil (a : ℝ) (γ : Polynomial ℝ) (x : ℝ) :
    (Work.BMF.dil a γ).eval x = γ.eval (a * x) := by
  simp only [Work.BMF.dil, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

theorem IntegralOnDilIff (n : ℕ) (γ : Polynomial ℝ) :
    Work.BMF.IntegralOn (n : ℝ) γ ↔ Work.BMF.IntegralOn 1 (Work.BMF.dil (n : ℝ) γ) := by
  have hfun : ∀ k : ℤ,
      (Work.BMF.dil (n : ℝ) γ).eval (1 * (k : ℝ)) = γ.eval ((n : ℝ) * (k : ℝ)) := by
    intro k
    simp [eval_dil]
  unfold Work.BMF.IntegralOn
  simp only [hfun]

end Work.N8
