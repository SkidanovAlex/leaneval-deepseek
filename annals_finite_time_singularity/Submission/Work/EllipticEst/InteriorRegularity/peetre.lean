import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

/-- The elementary pointwise estimate behind Peetre's inequality:
`1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖y‖ ^ 2)`, obtained from
`‖x‖ ≤ ‖x - y‖ + ‖y‖` and `2 * ‖x - y‖ * ‖y‖ ≤ ‖x - y‖ ^ 2 + ‖y‖ ^ 2`. -/
lemma one_add_norm_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
  have hnorm : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
  have hsq : ‖x‖ ^ 2 ≤ (‖x - y‖ + ‖y‖) ^ 2 := by
    nlinarith [hnorm, norm_nonneg x, norm_nonneg (x - y), norm_nonneg y]
  nlinarith [hsq, sq_nonneg (‖x - y‖ - ‖y‖)]

theorem peetre {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : ℝ) (x y : E) :
    (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ 2 ^ (|s| / 2) * (1 + ‖x - y‖ ^ 2) ^ (|s| / 2)
      * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
  have hpX : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hpA : (0 : ℝ) < 1 + ‖x - y‖ ^ 2 := by positivity
  have hpY : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rcases le_or_gt (0 : ℝ) s with hs | hs
  · -- `s ≥ 0` : raise the pointwise estimate to the power `s / 2`
    rw [abs_of_nonneg hs]
    have h := Real.rpow_le_rpow (le_of_lt hpX) (one_add_norm_sq_le x y)
      (by linarith : (0 : ℝ) ≤ s / 2)
    calc (1 + ‖x‖ ^ 2) ^ (s / 2)
        ≤ (2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖y‖ ^ 2)) ^ (s / 2) := h
      _ = 2 ^ (s / 2) * (1 + ‖x - y‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
          rw [Real.mul_rpow (x := 2 * (1 + ‖x - y‖ ^ 2)) (y := 1 + ‖y‖ ^ 2)
                (by positivity) (by positivity)]
          rw [Real.mul_rpow (x := 2) (y := 1 + ‖x - y‖ ^ 2) (by norm_num) (by positivity)]
  · -- `s < 0` : apply the previous case to the pair `(y, x)` with exponent `-s / 2`
    -- and cancel the two powers of the positive quantity `1 + ‖x‖ ^ 2`.
    rw [abs_of_neg hs]
    have ht : (0 : ℝ) < -s / 2 := by linarith
    have hkeyY : 1 + ‖y‖ ^ 2 ≤ 2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖x‖ ^ 2) := by
      simpa [norm_sub_rev] using one_add_norm_sq_le y x
    have hmono : (1 + ‖y‖ ^ 2) ^ (-s / 2) ≤
        2 ^ (-s / 2) * (1 + ‖x - y‖ ^ 2) ^ (-s / 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2) := by
      have h := Real.rpow_le_rpow (le_of_lt hpY) hkeyY (le_of_lt ht)
      calc (1 + ‖y‖ ^ 2) ^ (-s / 2)
          ≤ (2 * (1 + ‖x - y‖ ^ 2) * (1 + ‖x‖ ^ 2)) ^ (-s / 2) := h
        _ = 2 ^ (-s / 2) * (1 + ‖x - y‖ ^ 2) ^ (-s / 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2) := by
            rw [Real.mul_rpow (x := 2 * (1 + ‖x - y‖ ^ 2)) (y := 1 + ‖x‖ ^ 2)
                  (by positivity) (by positivity)]
            rw [Real.mul_rpow (x := 2) (y := 1 + ‖x - y‖ ^ 2) (by norm_num) (by positivity)]
    have hXt : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ (-s / 2) := Real.rpow_pos_of_pos hpX _
    have hYt : (0 : ℝ) < (1 + ‖y‖ ^ 2) ^ (-s / 2) := Real.rpow_pos_of_pos hpY _
    have hs2 : s / 2 = -(-s / 2) := by ring
    rw [hs2, Real.rpow_neg (le_of_lt hpX), Real.rpow_neg (le_of_lt hpY)]
    rw [inv_le_iff_one_le_mul₀ hXt]
    rw [show (2 ^ (-s / 2) * (1 + ‖x - y‖ ^ 2) ^ (-s / 2) * ((1 + ‖y‖ ^ 2) ^ (-s / 2))⁻¹)
          * (1 + ‖x‖ ^ 2) ^ (-s / 2)
        = (2 ^ (-s / 2) * (1 + ‖x - y‖ ^ 2) ^ (-s / 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2))
            / (1 + ‖y‖ ^ 2) ^ (-s / 2) from by rw [div_eq_mul_inv]; ring]
    rw [one_le_div₀ hYt]
    exact hmono

end Work.EllipticEst.InteriorRegularity
