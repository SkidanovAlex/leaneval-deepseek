import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-- Auxiliary: for `0 < d`, `d ^ (3/4) ≤ d + d ^ (1/2)`.
If `d ≤ 1` the exponent comparison `3/4 ≥ 1/2` gives `d^(3/4) ≤ d^(1/2)`; if `d ≥ 1`
the exponent comparison `3/4 ≤ 1` gives `d^(3/4) ≤ d`. -/
private lemma rpow_three_quarters_le (d : ℝ) (hdpos : 0 < d) :
    d ^ ((3 : ℝ) / 4) ≤ d + d ^ ((1 : ℝ) / 2) := by
  have hd : 0 ≤ d := le_of_lt hdpos
  have h2 : 0 ≤ d ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hd _
  rcases le_or_gt d 1 with h1 | h1
  · have h := Real.rpow_le_rpow_of_exponent_ge hdpos h1
      (by norm_num : ((1 : ℝ) / 2) ≤ 3 / 4)
    linarith
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt h1)
      (by norm_num : ((3 : ℝ) / 4) ≤ 1)
    rw [Real.rpow_one] at h
    linarith

lemma MulRpowNegQuarterLe (M Y : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) :
    M * (M / Y) ^ (-(1 / 4 : ℝ)) ≤ M + Real.sqrt (M * Y) := by
  rcases lt_or_eq_of_le hY with hYpos | hY0
  · rcases lt_or_eq_of_le hM with hMpos | hM0
    · -- main case: `0 < M`, `0 < Y`
      set d : ℝ := M / Y with hddef
      have hdpos : 0 < d := by rw [hddef]; exact div_pos hMpos hYpos
      have hd : 0 ≤ d := le_of_lt hdpos
      have hMd : M = d * Y := by
        rw [hddef]; exact (div_mul_cancel₀ M (ne_of_gt hYpos)).symm
      -- `d * d^(-1/4) = d^(3/4)`
      have hd3 : d ^ ((3 : ℝ) / 4) = d * d ^ (-(1 / 4 : ℝ)) := by
        have h := Real.rpow_add' hd (show (1 : ℝ) + (-(1 / 4)) ≠ 0 by norm_num)
        rw [show (1 : ℝ) + (-(1 / 4)) = 3 / 4 by norm_num, Real.rpow_one] at h
        exact h
      -- `√(M*Y) = Y * d^(1/2)`
      have hsqrt : Real.sqrt (M * Y) = Y * d ^ ((1 : ℝ) / 2) := by
        rw [hMd, mul_assoc, Real.sqrt_mul hd, Real.sqrt_mul_self hY, Real.sqrt_eq_rpow]
        ring
      have hkey := rpow_three_quarters_le d hdpos
      calc M * (M / Y) ^ (-(1 / 4 : ℝ)) = M * d ^ (-(1 / 4 : ℝ)) := by rw [hddef]
        _ = Y * (d * d ^ (-(1 / 4 : ℝ))) := by rw [hMd]; ring
        _ = Y * d ^ ((3 : ℝ) / 4) := by rw [← hd3]
        _ ≤ Y * (d + d ^ ((1 : ℝ) / 2)) := mul_le_mul_of_nonneg_left hkey hY
        _ = M + Real.sqrt (M * Y) := by rw [hsqrt, hMd]; ring
    · -- `M = 0`
      rw [← hM0, zero_mul, zero_mul, Real.sqrt_zero, add_zero]
  · -- `Y = 0`
    subst hY0
    simp [Real.zero_rpow]
    exact hM

end Work.BoseFixR
