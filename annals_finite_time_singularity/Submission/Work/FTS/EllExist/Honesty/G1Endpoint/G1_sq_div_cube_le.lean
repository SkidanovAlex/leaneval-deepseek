import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.Honesty.G1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.G1Endpoint

/-- Elementary algebra behind `G1_sq_div_cube_le`: since `G1 α m c x = x ^ (-a) · G1A α m c x`
with `a = G1a α m`, the quotient `G1 x²/x³` is `G1A x²/x^{2a+3}`; no sign hypothesis on `a`
is needed because `x ` is positive and hence `x ^ (2a+3) > 0`. -/
private lemma sq_mul_rpow_neg_div (x a A : ℝ) (hx : 0 < x) :
    (x ^ (-a) * A) ^ 2 / x ^ 3 = A ^ 2 / x ^ (2 * a + 3) := by
  have h1 : (x ^ (-a)) ^ 2 = x ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    have : (-a) * ((2 : ℕ) : ℝ) = -(2 * a) := by ring
    rw [this]
  have h2 : x ^ (-(2 * a)) * x ^ (2 * a + 3) = x ^ 3 := by
    rw [← Real.rpow_add hx]
    have : -(2 * a) + (2 * a + 3) = (3 : ℝ) := by ring
    rw [this]
    exact Real.rpow_natCast x 3
  have hxA : (x ^ (-a) * A) ^ 2 = x ^ (-(2 * a)) * A ^ 2 := by
    rw [mul_pow, h1]
  have key : x ^ (-(2 * a)) = x ^ 3 / x ^ (2 * a + 3) := by
    rw [eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hx _))]
    exact h2
  rw [hxA, key]
  field_simp

theorem G1_sq_div_cube_le {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (h : Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3))) :
    Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
      ≤ Work.FTS.EllExist.Honesty.G1M0 c / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by
  have hxpow : 0 < x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) :=
    Real.rpow_pos_of_pos hx _
  have hG1 : Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
      = Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
          / x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by
    rw [Work.FTS.EllExist.Honesty.G1_eq_zpow_mul_G1A,
      Work.FTS.EllExist.Honesty.G1s_eq_neg_G1a]
    exact sq_mul_rpow_neg_div x (Work.FTS.EllExist.Honesty.G1a α m)
      (Work.FTS.EllExist.Honesty.G1A α m c x) hx
  rw [hG1, div_le_iff₀ hxpow]
  calc Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)) := h
    _ = Work.FTS.EllExist.Honesty.G1M0 c / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
          * x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by ring

end Work.FTS.EllExist.Honesty.G1Endpoint
