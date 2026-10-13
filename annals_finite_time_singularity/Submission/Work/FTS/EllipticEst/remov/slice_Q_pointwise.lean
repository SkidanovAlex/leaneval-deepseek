import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- Elementary real inequality behind `slice_Q_pointwise`: for `s ^ 2 + t ^ 2 = 1` the
quadratic form `(s a + 2 t b - s c)(s a - 4 t b + 5 s c)` is dominated by
`4 s^2 a^2 + 7 b^2 + 7 c^2`.

Proof: the difference of the two sides equals
`3 s^2 a^2 + 2 (s a)(t b) - 4 (s a)(s c) - 14 (t b)(s c) + (7 + 8 t^2) b^2 + (7 + 5 s^2) c^2`,
and each cross term is bounded below by a weighted `2xy ≥ -(λ x^2 + y^2/λ)`:
* `2 (sa)(tb) ≥ -(s^2a^2 + t^2b^2)`,
* `-4 (sa)(sc) ≥ -(2 s^2a^2 + 2 s^2c^2)`,
* `-14 (tb)(sc) ≥ -(5 t^2b^2 + (49/5) s^2c^2)`.
Adding gives `N ≥ (7 + 2 t^2) b^2 + (7 - (34/5) s^2) c^2 ≥ 0` because `s^2 ≤ 1`. -/
private lemma slice_Q_aux (s t a b c : ℝ) (h : s ^ 2 + t ^ 2 = 1) :
    (s * a + 2 * t * b - s * c) * (s * a - 4 * t * b + 5 * s * c)
      ≤ 4 * s ^ 2 * a ^ 2 + 7 * b ^ 2 + 7 * c ^ 2 := by
  have hs1 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  have k1 : -((s * a) ^ 2 + (t * b) ^ 2) ≤ 2 * (s * a) * (t * b) := by
    nlinarith [sq_nonneg (s * a + t * b)]
  have k2 : -(2 * (s * a) ^ 2 + (2 * (s * c)) ^ 2 / 2) ≤ 2 * (s * a) * (-(2 * (s * c))) := by
    nlinarith [sq_nonneg (2 * (s * a) - 2 * (s * c))]
  have k3 : -(5 * (t * b) ^ 2 + (7 * (s * c)) ^ 2 / 5) ≤ 2 * (t * b) * (-(7 * (s * c))) := by
    nlinarith [sq_nonneg (5 * (t * b) - 7 * (s * c))]
  nlinarith [k1, k2, k3, hs1, sq_nonneg t, sq_nonneg b, sq_nonneg c]

theorem slice_Q_pointwise (θ a b c : ℝ) :
    (Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c)
        * (Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c)
      ≤ 4 * (Real.sin θ) ^ 2 * a ^ 2 + 7 * b ^ 2 + 7 * c ^ 2 := by
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  exact slice_Q_aux (Real.sin θ) (Real.cos θ) a b c h

end Work.FTS.EllipticEst.remov
