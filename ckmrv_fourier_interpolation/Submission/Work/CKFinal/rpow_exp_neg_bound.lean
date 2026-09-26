import Mathlib

namespace Work.CKFinal

/-- The function `u ↦ u ^ t * exp (-u)` on `[0, ∞)` is maximised at `u = t`, giving
the global bound `u ^ t * exp (-u) ≤ (t / e) ^ t`. -/
theorem rpow_exp_neg_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    u ^ t * Real.exp (-u) ≤ (t / Real.exp 1) ^ t := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rw [Real.rpow_zero, one_mul]
    have hz : ((0:ℝ) / Real.exp 1) = 0 := by simp
    rw [hz, Real.rpow_zero]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · rcases eq_or_lt_of_le hu with rfl | hupos
    · rw [Real.zero_rpow (ne_of_gt htpos), zero_mul]
      exact Real.rpow_nonneg (by positivity) t
    · rw [Real.rpow_def_of_pos hupos, Real.rpow_def_of_pos (div_pos htpos (Real.exp_pos 1))]
      rw [Real.log_div (ne_of_gt htpos) (Real.exp_ne_zero 1), Real.log_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_sub_one_of_pos (div_pos hupos htpos)
      rw [Real.log_div (ne_of_gt hupos) (ne_of_gt htpos)] at hlog
      have hmul : t * (Real.log u - Real.log t) ≤ t * (u / t - 1) :=
        mul_le_mul_of_nonneg_left hlog ht
      have hsimp : t * (u / t - 1) = u - t := by field_simp
      rw [hsimp] at hmul
      nlinarith [hmul]

end Work.CKFinal
