import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N1

/-- An elementary consequence of `Z ≤ C * Y ^ m` for `Y, Z ≥ 11`: the iterated logarithm
of `Z` exceeds that of `Y` by at most `log (m + |log C|)`. -/
theorem loglog_le (C : ℝ) (hC : 0 < C) (m : ℕ) (hm : 1 ≤ m) {Y Z : ℝ} (hY : 11 ≤ Y)
    (hZ : 11 ≤ Z) (hZY : Z ≤ C * Y ^ m) :
    Real.log (Real.log Z) ≤ Real.log (Real.log Y) + Real.log ((m : ℝ) + |Real.log C|) := by
  have hYpos : 0 < Y := by linarith
  have hZpos : 0 < Z := by linarith
  have hm0 : (0:ℝ) < (m:ℝ) := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  have hY1 : (1:ℝ) < Y := by linarith
  have hZ1 : (1:ℝ) < Z := by linarith
  have hlYpos : 0 < Real.log Y := Real.log_pos hY1
  have hlZpos : 0 < Real.log Z := Real.log_pos hZ1
  -- `Real.log Y ≥ 1` because `Y ≥ 11 > e`
  have hlY1 : (1:ℝ) ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hYpos]
    linarith [Real.exp_one_lt_three]
  -- `log Z ≤ log C + m * log Y`
  have h1 : Real.log Z ≤ Real.log C + (m:ℝ) * Real.log Y := by
    have h := Real.log_le_log hZpos hZY
    rwa [Real.log_mul (ne_of_gt hC) (pow_ne_zero m (ne_of_gt hYpos)), Real.log_pow] at h
  -- `log Z ≤ |log C| + m * log Y`
  have h2 : Real.log Z ≤ |Real.log C| + (m:ℝ) * Real.log Y := by
    have := le_abs_self (Real.log C)
    linarith [h1]
  have hsumpos : 0 < |Real.log C| + (m:ℝ) * Real.log Y := by
    have : (0:ℝ) < (m:ℝ) * Real.log Y := mul_pos hm0 hlYpos
    have := abs_nonneg (Real.log C)
    linarith
  have h3 : Real.log (Real.log Z) ≤ Real.log (|Real.log C| + (m:ℝ) * Real.log Y) :=
    Real.log_le_log hlZpos h2
  -- `|log C| + m * log Y ≤ (m + |log C|) * log Y` using `log Y ≥ 1`
  have h4 : |Real.log C| + (m:ℝ) * Real.log Y ≤ ((m:ℝ) + |Real.log C|) * Real.log Y := by
    have hnc : (0:ℝ) ≤ |Real.log C| := abs_nonneg _
    nlinarith [mul_nonneg hnc (sub_nonneg.mpr hlY1)]
  have h5 : Real.log (|Real.log C| + (m:ℝ) * Real.log Y) ≤
      Real.log (((m:ℝ) + |Real.log C|) * Real.log Y) :=
    Real.log_le_log hsumpos h4
  have hmabs : (0:ℝ) < (m:ℝ) + |Real.log C| := by
    have := abs_nonneg (Real.log C); linarith
  have h6 : Real.log (((m:ℝ) + |Real.log C|) * Real.log Y)
      = Real.log ((m:ℝ) + |Real.log C|) + Real.log (Real.log Y) := by
    rw [Real.log_mul (ne_of_gt hmabs) (ne_of_gt hlYpos)]
  calc Real.log (Real.log Z)
      ≤ Real.log (|Real.log C| + (m:ℝ) * Real.log Y) := h3
    _ ≤ Real.log (((m:ℝ) + |Real.log C|) * Real.log Y) := h5
    _ = Real.log ((m:ℝ) + |Real.log C|) + Real.log (Real.log Y) := h6
    _ = Real.log (Real.log Y) + Real.log ((m:ℝ) + |Real.log C|) := by ring

end Work.BMF.N1
