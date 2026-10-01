import Mathlib
import Submission.Work.ZeroFreeTables.tf72Fc_decay

namespace Work.ZeroFreeTables.XY

/-- The derivative of the (polynomial) test function `tf72poly lam` has derivative equal to
the second iterated derivative of `tf72poly lam`.

`tf72poly lam` is the polynomial `(λ/30)(2-λt)³(4+6λt+λ²t²)`, hence `C^∞`; consequently its
first derivative `deriv (tf72poly lam)` is differentiable everywhere, and by construction
`iteratedDeriv 2 (tf72poly lam) = deriv (deriv (tf72poly lam))`. -/
lemma hasDerivAt_deriv_tf72poly (lam t : ℝ) :
    HasDerivAt (deriv (tf72poly lam)) (iteratedDeriv 2 (tf72poly lam) t) t := by
  -- the second iterated derivative is the derivative of the first derivative
  have h2 : iteratedDeriv 2 (tf72poly lam) = deriv (deriv (tf72poly lam)) := by
    show iteratedDeriv ((1 : ℕ) + 1) (tf72poly lam) = deriv (deriv (tf72poly lam))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  -- `tf72poly lam` is a polynomial, hence `C^∞`
  have hcf : ContDiff ℝ 2 (tf72poly lam) := by unfold tf72poly; fun_prop
  -- so its first derivative is differentiable everywhere
  have hd : DifferentiableAt ℝ (deriv (tf72poly lam)) t := by
    have h : Differentiable ℝ (deriv (tf72poly lam)) := by
      have h' := ContDiff.differentiable_iteratedDeriv' 1 hcf
      simpa only [iteratedDeriv_one] using h'
    exact h t
  exact hd.hasDerivAt

end Work.ZeroFreeTables.XY
