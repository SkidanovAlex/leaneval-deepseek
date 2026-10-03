import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.AbelKernel

/-- The Abel kernel `(a^{−σ} − (a+1)^{−σ})/σ` is nonnegative and bounded above by
`log ((a+1)/a)` for `a ≥ 1` and `σ > 0`. -/
theorem abel_kernel_bounds (a : ℝ) (ha : 1 ≤ a) (σ : ℝ) (hσ : 0 < σ) :
    0 ≤ (a ^ (-σ) - (a + 1) ^ (-σ)) / σ ∧
      (a ^ (-σ) - (a + 1) ^ (-σ)) / σ ≤ Real.log ((a + 1) / a) := by
  have ha_pos : 0 < a := lt_of_lt_of_le one_pos ha
  have hb_pos : 0 < a + 1 := by linarith
  have hnum_nonneg : 0 ≤ a ^ (-σ) - (a + 1) ^ (-σ) := by
    have hle : (a + 1) ^ (-σ) ≤ a ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos ha_pos (by linarith) (by linarith)
    linarith
  have hnum_le : a ^ (-σ) - (a + 1) ^ (-σ) ≤ σ * (Real.log (a + 1) - Real.log a) := by
    have hA : 0 ≤ Real.log a := Real.log_nonneg ha
    have hAB : Real.log a ≤ Real.log (a + 1) := Real.log_le_log ha_pos (by linarith)
    have hu : 0 ≤ σ * (Real.log (a + 1) - Real.log a) :=
      mul_nonneg (le_of_lt hσ) (sub_nonneg.mpr hAB)
    have h1 : a ^ (-σ) = Real.exp (-(σ * Real.log a)) := by
      rw [Real.rpow_def_of_pos ha_pos]
      congr 1
      ring
    have h2 : (a + 1) ^ (-σ) = Real.exp (-(σ * Real.log (a + 1))) := by
      rw [Real.rpow_def_of_pos hb_pos]
      congr 1
      ring
    have hdecomp :
        Real.exp (-(σ * Real.log a)) - Real.exp (-(σ * Real.log (a + 1))) =
          Real.exp (-(σ * Real.log a)) *
            (1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))) := by
      rw [show -(σ * Real.log (a + 1)) =
            -(σ * Real.log a) + (-(σ * (Real.log (a + 1) - Real.log a))) by ring]
      rw [Real.exp_add]
      ring
    have hfac_nonneg : 0 ≤ 1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a))) := by
      have : Real.exp (-(σ * (Real.log (a + 1) - Real.log a))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      linarith
    have hfac_le : 1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a))) ≤
        σ * (Real.log (a + 1) - Real.log a) := by
      have h := Real.one_sub_le_exp_neg (σ * (Real.log (a + 1) - Real.log a))
      linarith
    have hexpA_le : Real.exp (-(σ * Real.log a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hA, le_of_lt hσ]
    have hprod :
        Real.exp (-(σ * Real.log a)) *
            (1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))) ≤
          σ * (Real.log (a + 1) - Real.log a) := by
      calc Real.exp (-(σ * Real.log a)) *
              (1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a))))
          ≤ 1 * (1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a)))) :=
            mul_le_mul_of_nonneg_right hexpA_le hfac_nonneg
        _ = 1 - Real.exp (-(σ * (Real.log (a + 1) - Real.log a))) := by ring
        _ ≤ σ * (Real.log (a + 1) - Real.log a) := hfac_le
    rw [h1, h2, hdecomp]
    exact hprod
  constructor
  · exact div_nonneg hnum_nonneg (le_of_lt hσ)
  · rw [Real.log_div (ne_of_gt hb_pos) (ne_of_gt ha_pos), div_le_iff₀ hσ]
    calc a ^ (-σ) - (a + 1) ^ (-σ)
        ≤ σ * (Real.log (a + 1) - Real.log a) := hnum_le
      _ = (Real.log (a + 1) - Real.log a) * σ := by ring

end Commons.Analysis.AbelKernel