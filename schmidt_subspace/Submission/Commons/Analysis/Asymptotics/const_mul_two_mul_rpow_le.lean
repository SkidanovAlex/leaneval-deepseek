import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotics

/-- For every positive real `a` there is a positive real `d` with `a ≤ 2 ^ d`. -/
lemma exists_two_rpow_ge_pos (a : ℝ) (ha : 0 < a) :
    ∃ d : ℝ, 0 < d ∧ a ≤ (2 : ℝ) ^ d := by
  refine ⟨max 1 (Real.log a / Real.log 2), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd : Real.log a ≤ Real.log 2 * max 1 (Real.log a / Real.log 2) := by
      have h1 : Real.log a / Real.log 2 ≤ max 1 (Real.log a / Real.log 2) := le_max_right _ _
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hlog2)
      have hc : Real.log 2 * (Real.log a / Real.log 2) = Real.log a := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hlog2)
      rwa [hc] at h2
    calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (Real.log 2 * max 1 (Real.log a / Real.log 2)) := Real.exp_le_exp.mpr hd
      _ = (2 : ℝ) ^ max 1 (Real.log a / Real.log 2) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Absorption of a constant factor into a power: for real `C, C' > 0` there is `D > 0` with
`C * N * (2 * N) ^ C' ≤ N ^ D` for every natural `N ≥ 2`.  (Take `D := C + C' + d` with
`2 ^ d ≥ C * 2 ^ (C' - C)`; then `N ^ D = N ^ (1 + C') * N ^ (C + d - C')` and
`N ^ (C + d - C') ≥ 2 ^ (C + d - C') ≥ C * 2 ^ (C' - C) * 2 ^ (C + d - C') · …`, i.e. the constant
`C * 2 ^ C'` is dominated by `2 ^ (C + d)`.) -/
theorem const_mul_two_mul_rpow_le {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N →
      C * (N : ℝ) * (2 * (N : ℝ)) ^ C' ≤ (N : ℝ) ^ D := by
  have h2C : 0 < (2 : ℝ) ^ C' := Real.rpow_pos_of_pos (by norm_num) C'
  have ha : 0 < C * (2 : ℝ) ^ C' := mul_pos hC h2C
  obtain ⟨d, hd, hda⟩ := exists_two_rpow_ge_pos (C * (2 : ℝ) ^ C') ha
  refine ⟨1 + C' + d, by linarith, ?_⟩
  intro N hN
  have hx2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hxnn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hx0
  have hmul : (2 * (N : ℝ)) ^ C' = (2 : ℝ) ^ C' * (N : ℝ) ^ C' :=
    Real.mul_rpow (by norm_num) hxnn
  have hxd : C * (2 : ℝ) ^ C' ≤ (N : ℝ) ^ d :=
    le_trans hda (Real.rpow_le_rpow (by norm_num) hx2 (le_of_lt hd))
  have hsplit : (N : ℝ) ^ (1 + C' + d) = (N : ℝ) ^ (1 + C') * (N : ℝ) ^ d := by
    rw [show (1 : ℝ) + C' + d = (1 + C') + d by ring, Real.rpow_add hx0]
  have hkey : (N : ℝ) * (N : ℝ) ^ C' = (N : ℝ) ^ (1 + C') := by
    rw [Real.rpow_add hx0 (1 : ℝ) C', Real.rpow_one]
  calc C * (N : ℝ) * (2 * (N : ℝ)) ^ C'
      = (C * (2 : ℝ) ^ C') * ((N : ℝ) * (N : ℝ) ^ C') := by rw [hmul]; ring
    _ = (C * (2 : ℝ) ^ C') * (N : ℝ) ^ (1 + C') := by rw [hkey]
    _ ≤ (N : ℝ) ^ d * (N : ℝ) ^ (1 + C') :=
          mul_le_mul_of_nonneg_right hxd (Real.rpow_nonneg hxnn _)
    _ = (N : ℝ) ^ (1 + C') * (N : ℝ) ^ d := by ring
    _ = (N : ℝ) ^ (1 + C' + d) := hsplit.symm

end Commons.Analysis.Asymptotics