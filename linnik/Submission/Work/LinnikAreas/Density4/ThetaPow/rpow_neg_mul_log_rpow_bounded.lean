import Mathlib

namespace Work.LinnikAreas.Density4.ThetaPow

/-- For `μ > 0` and `c ≥ 0`, the function `Q ↦ Q ^ (-μ) * (log (2 + Q)) ^ c` is bounded
above on `[1, ∞)`.  The proof gives the explicit constant `3 ^ (μ/2) / (μ/(2c)) ^ c`
(in the case `c > 0`), obtained from `log x ≤ x ^ a / a` with `a = μ / (2c)`, and the
trivial constant `1` when `c = 0`. -/
theorem rpow_neg_mul_log_rpow_bounded (μ c : ℝ) (hμ : 0 < μ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 1 ≤ Q → Q ^ (-μ) * (Real.log (2 + Q)) ^ c ≤ K := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- Case `c = 0`: the second factor is `1` and `Q ^ (-μ) ≤ 1`.
    refine ⟨1, one_pos, ?_⟩
    intro Q hQ
    have h1 : Q ^ (-μ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith)
    rw [← hc0, Real.rpow_zero, mul_one]
    exact h1
  · -- Case `c > 0`.  Put `a = μ / (2c)`, so that `a * c = μ / 2`.
    set a : ℝ := μ / (2 * c) with ha
    have hapos : 0 < a := by
      rw [ha]; positivity
    have h3μ : 0 < (3:ℝ) ^ (μ/2) := Real.rpow_pos_of_pos (by norm_num) _
    refine ⟨3 ^ (μ / 2) / a ^ c, ?_, ?_⟩
    · exact div_pos h3μ (Real.rpow_pos_of_pos hapos c)
    · intro Q hQ
      have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
      have h2Q : 0 ≤ 2 + Q := by linarith
      have hlog : 0 ≤ Real.log (2 + Q) := Real.log_nonneg (by linarith)
      -- `log (2 + Q) ≤ (2 + Q) ^ a / a`
      have step1 : Real.log (2 + Q) ≤ (2 + Q) ^ a / a := Real.log_le_rpow_div h2Q hapos
      have step2 : (Real.log (2 + Q)) ^ c ≤ ((2 + Q) ^ a / a) ^ c :=
        Real.rpow_le_rpow hlog step1 hc
      have hac : a * c = μ / 2 := by
        rw [ha]; field_simp
      -- `((2 + Q) ^ a / a) ^ c = (2 + Q) ^ (μ/2) / a ^ c`
      have step3 : ((2 + Q) ^ a / a) ^ c = (2 + Q) ^ (μ / 2) / a ^ c := by
        rw [Real.div_rpow (Real.rpow_nonneg h2Q a) (le_of_lt hapos) c]
        rw [← Real.rpow_mul h2Q a c, hac]
      rw [step3] at step2
      -- `Q ^ (-μ) * (2 + Q) ^ (μ/2) ≤ 3 ^ (μ/2)`
      have hQμ2 : Q ^ (-μ) * (2 + Q) ^ (μ / 2) ≤ 3 ^ (μ / 2) := by
        have hle : 2 + Q ≤ 3 * Q := by linarith
        have h1 : (2 + Q) ^ (μ/2) ≤ (3 * Q) ^ (μ/2) :=
          Real.rpow_le_rpow h2Q hle (by linarith)
        have h2 : (3 * Q) ^ (μ/2) = 3 ^ (μ/2) * Q ^ (μ/2) :=
          Real.mul_rpow (by norm_num) (le_of_lt hQpos)
        have h3 : Q ^ (-μ) * Q ^ (μ/2) = Q ^ (-μ/2) := by
          rw [← Real.rpow_add hQpos (-μ) (μ/2)]
          congr 1
          ring
        have h4 : Q ^ (-μ/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith)
        calc Q ^ (-μ) * (2 + Q) ^ (μ/2)
            ≤ Q ^ (-μ) * (3 ^ (μ/2) * Q ^ (μ/2)) := by
                rw [← h2]
                exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hQpos) _)
          _ = 3 ^ (μ/2) * (Q ^ (-μ) * Q ^ (μ/2)) := by ring
          _ = 3 ^ (μ/2) * Q ^ (-μ/2) := by rw [h3]
          _ ≤ 3 ^ (μ/2) * 1 := by
                exact mul_le_mul_of_nonneg_left h4 (le_of_lt h3μ)
          _ = 3 ^ (μ/2) := by ring
      calc Q ^ (-μ) * (Real.log (2 + Q)) ^ c
          ≤ Q ^ (-μ) * ((2 + Q) ^ (μ/2) / a^c) :=
              mul_le_mul_of_nonneg_left step2 (Real.rpow_nonneg (le_of_lt hQpos) _)
        _ = (Q ^ (-μ) * (2 + Q) ^ (μ/2)) / a^c := by ring
        _ ≤ 3 ^ (μ/2) / a^c :=
              div_le_div_of_nonneg_right hQμ2 (Real.rpow_nonneg (le_of_lt hapos) c)

end Work.LinnikAreas.Density4.ThetaPow
