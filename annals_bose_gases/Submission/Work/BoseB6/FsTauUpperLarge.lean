import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6

/-- **Upper bound for `τ̃` in the large-`t` regime** (FS §10, `eq:tautilde-Est`).

With `4 c₂ ≤ t` both truncations `[|t| − c₁]₊`, `[|t| − c₂]₊` are active, so
`τ̃(t) = (1−ε_T)(t−c₁)² + ε_T(t−c₂)²` and the claim is the elementary estimate

  `t² − τ̃(t) = 2 ε_T c₂ t + (2 − ε_T) c₂² − (1 − ε_T) c₁² ≥ 0`,

using `t ≥ 0`, `ε_T ≥ 0` and `c₂ ≥ c₁ ≥ 0` (so `c₂² ≥ c₁²`, `2 − ε_T ≥ 1 − ε_T`). -/
theorem FsTauUpperLarge {εT c1 c2 t : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (ht : 0 ≤ t) (h4 : 4 * c2 ≤ t) :
    Work.BoseB6.fsTau εT c1 c2 t ≤ t ^ 2 - 2 * c1 * (1 - εT) * t + 2 * c2 ^ 2 := by
  have hc2 : 0 ≤ c2 := le_trans hc1 hc12
  have h1 : 0 ≤ t - c1 := by linarith
  have h2 : 0 ≤ t - c2 := by linarith
  have e1 : max (|t| - c1) 0 = t - c1 := by rw [abs_of_nonneg ht, max_eq_left h1]
  have e2 : max (|t| - c2) 0 = t - c2 := by rw [abs_of_nonneg ht, max_eq_left h2]
  rw [fsTau, e1, e2]
  nlinarith [sq_nonneg (c2 - c1), mul_nonneg hε0 hc2, mul_nonneg (mul_nonneg hε0 hc2) ht,
    sq_nonneg (1 - εT), mul_nonneg hc2 hc2, mul_le_mul_of_nonneg_right hc12 hc2,
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc1 hc12 2)
      (by linarith : (0 : ℝ) ≤ 1 - εT)]

end Work.BoseB6
