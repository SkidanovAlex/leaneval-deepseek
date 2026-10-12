import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- Arithmetic inequality used in the Lee--Huang--Yang two-quadratic estimate.

Writing `C` for the coefficient of `π` and `D` for the rational part on the
right-hand side, the difference of the two sides equals `π * C + D` with

* `C = (10/9)(x-w)^2 - 4w^2 + 4(x+1)(1 - x/20) - 272w`,
* `D = -(1/40)x(x+1) - (x-8w)x`.

Under `w ≥ 20` and `x ≥ 8w` one has `C ≥ 0`, so `π C ≥ 3.14 C`; and
`3.14 C + D ≥ 0` follows from `w ≥ 20` and `x ≥ 8w` by elementary polynomial
arithmetic (both `C` and `3.14 C + D` are increasing in `x ≥ 8w`; the
left hypothesis `x ≤ 9w` is not needed). -/
lemma arithSimpleA2TwoQuad {x w : ℝ} (hw : 20 ≤ w) (hl : 8 * w ≤ x) (hu : x ≤ 9 * w) :
    (1 / 9) * (x - w) ^ 2 * (8 * Real.pi)
      ≤ (1 / 4) * (x - w) ^ 2 * (8 * Real.pi) - 4 * Real.pi * w ^ 2
        + 4 * Real.pi * (x + 1) * (1 - x / 20)
        - (1 / 40) * x * (x + 1) - (x - 8 * w) * x - 272 * Real.pi * w := by
  have hxu : x ≤ 9 * w := hu
  have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  -- The coefficient `C` of `π` is nonnegative under the hypotheses.
  have hC : 0 ≤ (10 / 9 : ℝ) * (x - w) ^ 2 - 4 * w ^ 2
      + 4 * (x + 1) * (1 - x / 20) - 272 * w := by
    nlinarith [sq_nonneg (x - 8 * w), sq_nonneg (x - w), sq_nonneg (w - 20)]
  -- Replacing `π` by `3.14` leaves a nonnegative polynomial.
  have hF : 0 ≤ (3.14 : ℝ) * ((10 / 9 : ℝ) * (x - w) ^ 2 - 4 * w ^ 2
        + 4 * (x + 1) * (1 - x / 20) - 272 * w)
      - (1 / 40) * x * (x + 1) - (x - 8 * w) * x := by
    nlinarith [sq_nonneg (x - 8 * w), sq_nonneg (x - w), sq_nonneg (w - 20),
      mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hl)]
  have hπC := mul_le_mul_of_nonneg_right hπ.le hC
  nlinarith [hπC, hF, hxu]

end Work.MGroupInput
