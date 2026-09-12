import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

open scoped Topology

/-- For `1 ≤ m`, the `(2k)`-th real roots of `m` approach `1` from above:
given any `η > 0` there is `k ≥ 1` with `m ^ (1/(2k)) < 1 + η`.
(Here all exponents are real powers `Real.rpow`.) -/
theorem rpow_root_tendsto_one (m : ℕ) (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ (m : ℝ) ^ (((2 * k : ℕ) : ℝ)⁻¹) < 1 + η := by
  by_cases hm1 : m = 1
  · refine ⟨1, by norm_num, ?_⟩
    have hcast : (m : ℝ) = 1 := by exact_mod_cast hm1
    rw [hcast]
    have : (1 : ℝ) < 1 + η := by linarith
    simpa [Real.one_rpow] using this
  · -- now m ≥ 2
    have hm2 : 2 ≤ m := by omega
    have ha2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have ha1 : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) ha2
    have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one ha1
    have hlog_m : 0 < Real.log (m : ℝ) := Real.log_pos ha1
    have h_one_add : (1 : ℝ) < 1 + η := by linarith
    have h_one_add_pos : 0 < 1 + η := lt_trans zero_lt_one h_one_add
    have hlog_eta : 0 < Real.log (1 + η) := Real.log_pos h_one_add
    have htwo : 0 < (2 : ℝ) * Real.log (1 + η) := mul_pos (by norm_num) hlog_eta
    -- choose k large enough
    obtain ⟨k, hk⟩ := exists_nat_gt (Real.log (m : ℝ) / ((2 : ℝ) * Real.log (1 + η)))
    -- k ≥ 1
    have hx_nonneg : 0 ≤ Real.log (m : ℝ) / ((2 : ℝ) * Real.log (1 + η)) := by
      positivity
    have hk1 : 1 ≤ k := by
      have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hx_nonneg hk
      have : 0 < k := by exact_mod_cast hkpos
      omega
    -- strict inequality between logs
    have hk_mul : Real.log (m : ℝ) < (k : ℝ) * ((2 : ℝ) * Real.log (1 + η)) :=
      (div_lt_iff₀ htwo).mp hk
    have hck_pos : 0 < (((2 * k : ℕ) : ℝ)) := by
      have : 0 < 2 * k := by omega
      exact_mod_cast this
    have hk_div : Real.log (m : ℝ) / (((2 * k : ℕ) : ℝ)) < Real.log (1 + η) := by
      apply (div_lt_iff₀ hck_pos).mpr
      -- log m < (2k:ℝ) * log (1+η)
      have hcast : (((2 * k : ℕ) : ℝ)) = (k : ℝ) * (2 : ℝ) := by
        rw [Nat.cast_mul]
        ring
      calc
        Real.log (m : ℝ) < (k : ℝ) * ((2 : ℝ) * Real.log (1 + η)) := hk_mul
        _ = Real.log (1 + η) * (((2 * k : ℕ) : ℝ)) := by
          rw [hcast]
          ring
    -- now conclude
    refine ⟨k, hk1, ?_⟩
    rw [Real.rpow_def_of_pos hmpos]
    rw [← Real.exp_log h_one_add_pos]
    rw [Real.exp_lt_exp]
    calc
      Real.log (m : ℝ) * (((2 * k : ℕ) : ℝ)⁻¹)
          = Real.log (m : ℝ) / (((2 * k : ℕ) : ℝ)) := by
              field_simp [hck_pos.ne']
      _ < Real.log (1 + η) := hk_div

end Commons.Analysis.Real
