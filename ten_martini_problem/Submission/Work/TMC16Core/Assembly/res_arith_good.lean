import Mathlib

namespace Work.TMC16Core.Assembly

/-- Auxiliary: `min j (qn - j) ≥ 2j - 7 qn / 8` under `j ≤ 5 qn / 8`. -/
private lemma aux_min_ge {qn j : ℕ} (hj : (j : ℝ) ≤ 5 * (qn : ℝ) / 8) :
    2 * (j : ℝ) - 7 * (qn : ℝ) / 8 ≤ min (j : ℝ) ((qn : ℝ) - (j : ℝ)) := by
  have hq_nonneg : (0 : ℝ) ≤ (qn : ℝ) := Nat.cast_nonneg _
  apply le_min
  · nlinarith [hj, hq_nonneg]
  · nlinarith [hj]

theorem res_arith_good {L εf : ℝ} (hL : 0 < L) (hεf : 0 < εf) {qn j d : ℕ}
    (hj : (j : ℝ) ≤ 5 * (qn : ℝ) / 8)
    (hd : (d : ℝ) = min (j : ℝ) ((qn : ℝ) - (j : ℝ)))
    (hlog : Real.log 2 ≤ L + (19 / 8) * εf * (qn : ℝ) + εf) :
    2 * Real.exp (-(L / 2) * (d : ℝ)) * Real.exp (((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)) ≤
      Real.exp ((2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf)) := by
  -- Key inequality: `d ≥ 2j - 7 qn / 8`, equivalently `j - d/2 - 7 qn/16 ≤ 0`.
  have hmax : 2 * (j : ℝ) - 7 * (qn : ℝ) / 8 ≤ (d : ℝ) := by
    rw [hd]; exact aux_min_ge hj
  have key1 : (j : ℝ) - (d : ℝ) / 2 - 7 * (qn : ℝ) / 16 ≤ 0 := by linarith [hmax]
  have key2 : (j : ℝ) - 5 * (qn : ℝ) / 8 ≤ 0 := by linarith [hj]
  have hprod1 : L * ((j : ℝ) - (d : ℝ) / 2 - 7 * (qn : ℝ) / 16) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL) key1
  have hprod2 : εf * ((j : ℝ) - 5 * (qn : ℝ) / 8) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hεf) key2
  -- The inequality on exponents.
  have hmain : Real.log 2 + (-(L / 2) * (d : ℝ)) + ((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)
      ≤ (2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf) := by
    nlinarith [hlog, hprod1, hprod2]
  have hlog2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  calc 2 * Real.exp (-(L / 2) * (d : ℝ)) * Real.exp (((qn : ℝ) - 1 + (j : ℝ)) * (L + εf))
      = Real.exp (Real.log 2) * Real.exp (-(L / 2) * (d : ℝ)) *
          Real.exp (((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)) := by rw [hlog2]
    _ = Real.exp (Real.log 2 + (-(L / 2) * (d : ℝ))) *
          Real.exp (((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)) := by rw [← Real.exp_add]
    _ = Real.exp (Real.log 2 + (-(L / 2) * (d : ℝ)) +
          ((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)) := by rw [← Real.exp_add]
    _ ≤ Real.exp ((2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf)) := Real.exp_le_exp.mpr hmain

end Work.TMC16Core.Assembly
