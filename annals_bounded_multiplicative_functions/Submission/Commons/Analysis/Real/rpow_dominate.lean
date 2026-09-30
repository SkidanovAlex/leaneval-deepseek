import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Real

theorem rpow_dominate {a M : ℝ} (ha0 : 0 ≤ a) (haM : a ≤ M) (hM : 0 ≤ M)
    {p p0 : ℝ} (hp0 : 0 ≤ p0) (hp0p : p0 ≤ p) :
    a ^ p ≤ M ^ (p - p0) * a ^ p0 := by
  rcases eq_or_lt_of_le ha0 with ha0eq | ha0pos
  · -- a = 0
    subst a
    by_cases hp : p = 0
    · have hp0eq : p0 = 0 := by linarith
      have hdiff0 : p - p0 = 0 := by linarith
      rw [hdiff0, hp, hp0eq]
      norm_num
    · have hMpow : 0 ≤ M ^ (p - p0) :=
        Real.rpow_nonneg hM (p - p0)
      rw [Real.zero_rpow hp]
      exact mul_nonneg hMpow (Real.zero_rpow_nonneg p0)
  · -- 0 < a
    have hdiff : 0 ≤ p - p0 := sub_nonneg.mpr hp0p
    have hpp : p = (p - p0) + p0 := by ring
    have hmain : a ^ p = a ^ (p - p0) * a ^ p0 := by
      rw [← Real.rpow_add ha0pos (p - p0) p0, ← hpp]
    rw [hmain]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ha0 haM hdiff) (Real.rpow_nonneg ha0 p0)

end Commons.Analysis.Real