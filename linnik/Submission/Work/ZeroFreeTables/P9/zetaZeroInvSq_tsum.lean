import Mathlib
import Submission.Work.ZeroFreeTables.P9.zeta_zeroSum_invSq_tsum

/-!
# Uniform inverse-square bound for the zeros of the completed Riemann zeta function on `‖s‖ ≤ 5`

The Poisson-kernel (inverse-square) zero sum of `Λ = completedRiemannZeta`,
`∑' u, ord_u(Λ) · 1/(1 + ‖s - u‖²)`, is bounded uniformly for `s` in the fixed ball `‖s‖ ≤ 5`.

This is the restriction to `‖s‖ ≤ 5` of the already available uniform bound
`Work.ZeroFreeTables.P9.zeta_zeroSum_invSq_tsum`, which holds on the larger ball `‖s‖ ≤ 11`.

NOTE.  The bound is *not* special to `5`: for every `R` the uniform bound on `‖s‖ ≤ R` follows
in the same way, the point of the constant `5` being only that it is the range required here.
-/

namespace Work.ZeroFreeTables.P9

theorem zetaZeroInvSq_tsum :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖s‖ ≤ 5 →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := zeta_zeroSum_invSq_tsum
  exact ⟨C, hCpos, fun s hs => hC s (le_trans hs (by norm_num))⟩

end Work.ZeroFreeTables.P9
