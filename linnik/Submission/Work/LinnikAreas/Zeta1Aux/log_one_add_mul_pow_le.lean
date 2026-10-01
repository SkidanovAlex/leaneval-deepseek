import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- For every `G > 0` there is `C₂ > 0` with
`log (1 + 4·G·(|v| + 9)^13) ≤ C₂ · log (|v| + 3)` for all `|v| ≥ 7`.

Route: `(|v| + 9)^13 ≥ 1`, hence `1 + 4G(|v|+9)^13 ≤ (1 + 4G)(|v|+9)^13`, so
`log ≤ log (1+4G) + 13 log (|v|+9)`; and `|v| + 9 ≤ 2(|v| + 3)`, so
`log (|v|+9) ≤ log 2 + log (|v|+3)`; finally `log (|v|+3) ≥ 1` (as `|v|+3 ≥ 10 > e`)
absorbs both `log (1+4G)` and `log 2`. -/
lemma log_one_add_mul_pow_le (G : ℝ) (hG : 0 < G) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ v : ℝ, 7 ≤ |v| →
      Real.log (1 + 4 * G * (|v| + 9) ^ 13) ≤ C₂ * Real.log (|v| + 3) := by
  refine ⟨Real.log (1 + 4 * G) + 13 * Real.log 2 + 13, ?_, ?_⟩
  · have hA : 0 ≤ Real.log (1 + 4 * G) := Real.log_nonneg (by linarith)
    have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · intro v hv
    have hA : 0 ≤ Real.log (1 + 4 * G) := Real.log_nonneg (by linarith)
    have hL : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
    -- |v| + 3 ≥ 10 > e, so log (|v|+3) ≥ 1
    have h10 : 1 < Real.log 10 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hB : 1 ≤ Real.log (|v| + 3) := by
      have h3 : (10 : ℝ) ≤ |v| + 3 := by linarith [hv]
      exact (le_of_lt h10).trans (Real.log_le_log (by norm_num) h3)
    -- positivity bookkeeping
    have h9pos : (0 : ℝ) < |v| + 9 := by positivity
    have h9nn : (0 : ℝ) ≤ |v| + 9 := le_of_lt h9pos
    have hpow_nn : (0 : ℝ) ≤ (|v| + 9) ^ 13 := pow_nonneg h9nn 13
    have hpow_pos : (0 : ℝ) < (|v| + 9) ^ 13 := pow_pos h9pos 13
    have ha1 : (1 : ℝ) ≤ (|v| + 9) ^ 13 := one_le_pow₀ (by linarith [hv])
    have hposarg : (0 : ℝ) < 1 + 4 * G * (|v| + 9) ^ 13 := by
      have : (0 : ℝ) ≤ 4 * G * (|v| + 9) ^ 13 :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hG)) hpow_nn
      linarith
    -- step 1
    have hstep1 : Real.log (1 + 4 * G * (|v| + 9) ^ 13) ≤
        Real.log (1 + 4 * G) + 13 * Real.log (|v| + 9) := by
      have hle : 1 + 4 * G * (|v| + 9) ^ 13 ≤ (1 + 4 * G) * (|v| + 9) ^ 13 := by
        nlinarith [ha1]
      have h14Gpos : (0 : ℝ) < 1 + 4 * G := by linarith
      calc Real.log (1 + 4 * G * (|v| + 9) ^ 13)
          ≤ Real.log ((1 + 4 * G) * (|v| + 9) ^ 13) :=
            Real.log_le_log hposarg hle
        _ = Real.log (1 + 4 * G) + Real.log ((|v| + 9) ^ 13) :=
            Real.log_mul (ne_of_gt h14Gpos) (ne_of_gt hpow_pos)
        _ = Real.log (1 + 4 * G) + 13 * Real.log (|v| + 9) := by
            rw [Real.log_pow]; norm_num
    -- step 2
    have hstep2 : Real.log (|v| + 9) ≤ Real.log 2 + Real.log (|v| + 3) := by
      have hle : |v| + 9 ≤ 2 * (|v| + 3) := by linarith [hv]
      have h3pos : (0 : ℝ) < |v| + 3 := by positivity
      calc Real.log (|v| + 9) ≤ Real.log (2 * (|v| + 3)) :=
            Real.log_le_log h9pos hle
        _ = Real.log 2 + Real.log (|v| + 3) :=
            Real.log_mul (by norm_num) (ne_of_gt h3pos)
    have hAL : 0 ≤ Real.log (1 + 4 * G) + 13 * Real.log 2 := by linarith
    have hfinal :
        Real.log (1 + 4 * G) + 13 * (Real.log 2 + Real.log (|v| + 3)) ≤
          (Real.log (1 + 4 * G) + 13 * Real.log 2 + 13) * Real.log (|v| + 3) := by
      have h1 := mul_le_mul_of_nonneg_left hB hAL
      nlinarith [h1]
    calc Real.log (1 + 4 * G * (|v| + 9) ^ 13)
        ≤ Real.log (1 + 4 * G) + 13 * Real.log (|v| + 9) := hstep1
      _ ≤ Real.log (1 + 4 * G) + 13 * (Real.log 2 + Real.log (|v| + 3)) := by linarith
      _ ≤ (Real.log (1 + 4 * G) + 13 * Real.log 2 + 13) * Real.log (|v| + 3) := hfinal

end Work.LinnikAreas.Zeta1Aux
