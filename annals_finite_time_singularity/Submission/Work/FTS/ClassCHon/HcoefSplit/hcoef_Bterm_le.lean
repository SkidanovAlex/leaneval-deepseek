import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem hcoef_Bterm_le {α β : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hβ : 0 ≤ β) {m : ℕ}
    (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))))
      ≤ (β / α) * (1 / 2 : ℝ) ^ m := by
  -- Throughout, `P = rgP α m = 2m/α` is the growing exponent, `Q = rgQ α m = (2m+5)/α`
  -- the decaying one, `K = rgK α m = 1/(α(4m+5))` the normalisation, and `E = eNorm m ≥ 1`.
  -- The two exponential coefficients are estimated by `2^{-Q} ≤ 2^{-P} ≤ 2^{-m} = (1/2)^m`,
  -- the two square-root factors by `1/√(2Q-1) ≤ 1`, `1/√(2P-3) ≤ 1`, and the algebraic
  -- prefactor by `(m+1)/(α(4m+5)) ≤ (1/2)(1/α)`.
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hE : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m :=
    (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).1
  -- `P ≥ 8m`: since `α ≤ 1/4`, `2m/α ≥ 8m`.
  have hP8 : 8 * (m : ℝ) ≤ Work.FTS.EllExist.rgP α m := by
    rw [Work.FTS.EllExist.rgP, le_div_iff₀ hα]
    nlinarith [mul_le_mul_of_nonneg_left hα4 hm0]
  have hPm : (m : ℝ) ≤ Work.FTS.EllExist.rgP α m := by
    have : (m : ℝ) ≤ 8 * (m : ℝ) := by linarith
    linarith
  -- `Q ≥ 20`: since `α ≤ 1/4`, `(2m+5)/α ≥ 5/α ≥ 20`.
  have hQ20 : 20 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    linarith
  have hPQ : Work.FTS.EllExist.rgP α m ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgP, Work.FTS.EllExist.rgQ]
    exact div_le_div_of_nonneg_right (by linarith) hα.le
  have hQmono : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
      ≤ (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hPhalf : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) ≤ (1 / 2 : ℝ) ^ m := by
    calc (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m)) ≤ (2 : ℝ) ^ (-(m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (1 / 2 : ℝ) ^ m := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  have ht1 : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
      / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) ≤ (1 / 2 : ℝ) ^ m :=
    le_trans (div_le_self (Real.rpow_nonneg (by norm_num) _)
      (Real.one_le_sqrt.mpr (by linarith))) (le_trans hQmono hPhalf)
  have ht2 : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
      / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) ≤ (1 / 2 : ℝ) ^ m :=
    le_trans (div_le_self (Real.rpow_nonneg (by norm_num) _)
      (Real.one_le_sqrt.mpr (by linarith))) hPhalf
  have hbr : (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
      + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) ≤ 2 * (1 / 2 : ℝ) ^ m := by
    have h := add_le_add ht1 ht2
    linarith
  have hbrnn : 0 ≤ (2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
      + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
        / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3) := by positivity
  have hA : ((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m ≤ (1 / 2) * (1 / α) := by
    rw [Work.FTS.EllExist.rgK]
    field_simp
    nlinarith [hm1]
  have hB : β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≤ β :=
    div_le_self hβ (Real.one_le_sqrt.mpr hE)
  have hAnn : (0 : ℝ) ≤ ((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m := by
    rw [Work.FTS.EllExist.rgK]; positivity
  have hBnn : (0 : ℝ) ≤ β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    positivity
  have hBC : (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
        + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))
      ≤ β * (2 * (1 / 2 : ℝ) ^ m) := mul_le_mul hB hbr hbrnn hβ
  have hBCleft : (0 : ℝ) ≤ (β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
      * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
        + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
          / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)) := mul_nonneg hBnn hbrnn
  have hAnn2 : (0 : ℝ) ≤ (1 / 2) * (1 / α) := by positivity
  rw [show ((m : ℝ) + 1) * (Work.FTS.EllExist.rgK α m
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))))
      = (((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m)
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) from by ring]
  calc (((m : ℝ) + 1) * Work.FTS.EllExist.rgK α m)
        * ((β / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
              + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
                / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3)))
      ≤ ((1 / 2) * (1 / α)) * (β * (2 * (1 / 2 : ℝ) ^ m)) := mul_le_mul hA hBC hBCleft hAnn2
    _ = (β / α) * (1 / 2 : ℝ) ^ m := by ring

end Work.FTS.ClassCHon.HcoefSplit
