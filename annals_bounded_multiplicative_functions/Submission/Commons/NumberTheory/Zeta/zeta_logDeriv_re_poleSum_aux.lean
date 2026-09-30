import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_poleSum_bound1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.Zeta

theorem zeta_logDeriv_re_poleSum_aux :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 →
        ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        (-deriv riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
          - (1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1) := by
  exact zeta_logDeriv_re_poleSum_bound1

end Commons.NumberTheory.Zeta
