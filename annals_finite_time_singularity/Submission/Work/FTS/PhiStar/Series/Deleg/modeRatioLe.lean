import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem modeRatioLe (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  -- Unfold the eigenvalue `lam m = 2m(2m+5) = 2M(2M+5)` with `M = (m:ℝ)`.
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
  -- The denominator is positive, as is `M^{3/2}`.
  have hYpos : (0 : ℝ) < 2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1) := by
    positivity
  have hrpos : (0 : ℝ) < (m : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hmpos _
  -- `M^{3/2} = M √M`.
  have hpow : (m : ℝ) ^ (3 / 2 : ℝ) = (m : ℝ) * Real.sqrt (m : ℝ) := by
    have h32 : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h32, Real.rpow_add hmpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  -- Clear the two positive denominators: it suffices to prove
  -- `√((2M+2)(2M+3)) · M^{3/2} ≤ (5/4)·2M(2M+5)·√(2M+1)`.
  rw [div_le_iff₀ hYpos]
  rw [show (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹
          * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1))
        = ((5 / 4) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1)))
            / ((m : ℝ) ^ (3 / 2 : ℝ)) from by ring]
  rw [le_div_iff₀ hrpos]
  rw [hpow]
  -- `√((2M+2)(2M+3)) ≤ 2M+3` since `(2M+2)(2M+3) ≤ (2M+3)^2`.
  have hsqrtA : Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 2 * (m : ℝ) + 3 := by
    calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        ≤ Real.sqrt ((2 * (m : ℝ) + 3) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (m : ℝ) + 3 := Real.sqrt_sq (by linarith)
  -- `√M ≤ √(2M+1)`.
  have hsqrtM : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * ((m : ℝ) * Real.sqrt (m : ℝ))
      ≤ (2 * (m : ℝ) + 3) * ((m : ℝ) * Real.sqrt (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrtA (by positivity)
    _ ≤ (2 * (m : ℝ) + 3) * ((m : ℝ) * Real.sqrt (2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrtM hmnn) (by linarith)
    _ ≤ ((5 / 2) * (2 * (m : ℝ) + 5)) * ((m : ℝ) * Real.sqrt (2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 5 / 4 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring

end Work.FTS.PhiStar.Series.Deleg
