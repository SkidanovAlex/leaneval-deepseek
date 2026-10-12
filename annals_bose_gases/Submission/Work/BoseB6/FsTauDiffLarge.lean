import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6

/-- Elementary upper bound for the Bogoliubov correction in the "large `t`" regime
`t ≥ 4 c₂`.  Since `4 c₂ ≤ t` forces `t ≥ c₁ ≥ 0` (as `c₁ ≤ c₂`), both `max`-clamps in
`fsTau` are inactive and the difference is a polynomial:
`t² - τ̃(t) = 2(1-ε_T)c₁t + 2ε_Tc₂t - (1-ε_T)c₁² - ε_Tc₂² ≤ 8(c₁ + ε_Tc₂)t`. -/
theorem FsTauDiffLarge {εT c1 c2 t : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (ht : 0 ≤ t) (h4 : 4 * c2 ≤ t) :
    t ^ 2 - Work.BoseB6.fsTau εT c1 c2 t ≤ 8 * (c1 + εT * c2) * t := by
  have ht1 : c1 ≤ t := by linarith
  have ht2 : c2 ≤ t := by linarith
  have hc2 : 0 ≤ c2 := le_trans hc1 hc12
  rw [fsTau, abs_of_nonneg ht, max_eq_left (by linarith : (0 : ℝ) ≤ t - c1),
    max_eq_left (by linarith : (0 : ℝ) ≤ t - c2)]
  nlinarith [sq_nonneg c1, sq_nonneg c2, sq_nonneg (c1 * t), sq_nonneg (c2 * t),
    mul_nonneg hc1 ht, mul_nonneg hc2 ht, mul_nonneg hε0 (mul_nonneg hc1 ht),
    mul_nonneg hε0 (mul_nonneg hc2 ht), mul_nonneg hε0 (sq_nonneg c1),
    mul_nonneg hε0 (sq_nonneg c2), hε0, hε1, hc1, hc2, ht, h4]

end Work.BoseB6
