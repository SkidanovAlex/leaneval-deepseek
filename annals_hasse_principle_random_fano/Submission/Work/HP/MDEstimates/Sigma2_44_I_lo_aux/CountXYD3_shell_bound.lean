import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.pair_counts

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

/-- Dyadic-shell form of the pair count for `(n,r) = (4,3)`: on the shell where the two
norms are powers of two `X = 2^{q.1}`, `Y = 2^{q.2}` and `2^{q.1+q.2} ≤ 4Δ` (so that the
third successive minimum is at most `4Δ/2^{q.1+q.2} ≥ 1`), the count is `≪ Δ³ log(8Δ)²`.

This is the asymmetric pair count `Work.HP.pair_counts 4 3` evaluated on the shell; the
key point is that `X·Y·(4Δ/(X·Y)) = 4Δ` kills the shell weights, leaving only `Δ³`. -/
theorem CountXYD3_shell_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∀ q : ℕ × ℕ,
      (2:ℝ) ^ (q.1 + q.2) ≤ 4 * Δ →
      (Work.HP.ellXY 4 3 ((2:ℝ) ^ q.1) ((2:ℝ) ^ q.2) (4 * Δ / (2:ℝ) ^ (q.1 + q.2)) : ℝ)
        ≤ C * Δ ^ 3 * Real.log (8 * Δ) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := Work.HP.pair_counts 4 (by norm_num) 3 (by norm_num) (by norm_num)
  refine ⟨64 * K, by positivity, ?_⟩
  intro Δ hΔ q hq
  set A : ℝ := (2:ℝ) ^ q.1 with hA_def
  set B : ℝ := (2:ℝ) ^ q.2 with hB_def
  set s : ℝ := (2:ℝ) ^ (q.1 + q.2) with hs_def
  have hs0 : 0 < s := by rw [hs_def]; positivity
  have hA1 : 1 ≤ A := by rw [hA_def]; exact one_le_pow₀ (by norm_num)
  have hB1 : 1 ≤ B := by rw [hB_def]; exact one_le_pow₀ (by norm_num)
  have hs1 : 1 ≤ s := by rw [hs_def]; exact one_le_pow₀ (by norm_num)
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hq' : s ≤ 4 * Δ := by rw [hs_def]; exact hq
  have hD1 : 1 ≤ 4 * Δ / s := by
    rw [one_le_div hs0]; exact hq'
  -- `2 * D ≤ 8 * Δ` and `0 ≤ log (2 * D)`, so the log factor is monotone
  have h2D : 2 * (4 * Δ / s) = 8 * Δ / s := by ring
  have h2D1 : 1 ≤ 2 * (4 * Δ / s) := by linarith
  have h2Dle : 2 * (4 * Δ / s) ≤ 8 * Δ := by
    rw [h2D, div_le_iff₀ hs0]
    nlinarith [hs1, hΔ0]
  have h2D0 : 0 < 2 * (4 * Δ / s) := lt_of_lt_of_le zero_lt_one h2D1
  have hlog : Real.log (2 * (4 * Δ / s)) ^ 2 ≤ Real.log (8 * Δ) ^ 2 := by
    have h1 : Real.log (2 * (4 * Δ / s)) ≤ Real.log (8 * Δ) := Real.log_le_log h2D0 h2Dle
    have h0 : 0 ≤ Real.log (2 * (4 * Δ / s)) := Real.log_nonneg h2D1
    nlinarith [h1, h0]
  have hh := hK A B (4 * Δ / s) hA1 hB1 hD1
  -- `X · Y · D = 4Δ`
  have hABD : A * B * (4 * Δ / s) = 4 * Δ := by
    have hAB : A * B = s := by rw [hA_def, hB_def, hs_def, pow_add]
    rw [hAB]; field_simp
  have hpow : A ^ 3 * B ^ 3 * (4 * Δ / s) ^ 3 = 64 * Δ ^ 3 := by
    calc A ^ 3 * B ^ 3 * (4 * Δ / s) ^ 3 = (A * B * (4 * Δ / s)) ^ 3 := by ring
      _ = (4 * Δ) ^ 3 := by rw [hABD]
      _ = 64 * Δ ^ 3 := by ring
  calc (Work.HP.ellXY 4 3 A B (4 * Δ / s) : ℝ)
      ≤ K * A ^ 3 * B ^ 3 * (4 * Δ / s) ^ 3 * Real.log (2 * (4 * Δ / s)) ^ 2 := by
        simpa using hh
    _ = 64 * K * Δ ^ 3 * Real.log (2 * (4 * Δ / s)) ^ 2 := by
        rw [show K * A ^ 3 * B ^ 3 * (4 * Δ / s) ^ 3 =
              K * (A ^ 3 * B ^ 3 * (4 * Δ / s) ^ 3) by ring, hpow]
        ring
    _ ≤ 64 * K * Δ ^ 3 * Real.log (8 * Δ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hlog
        positivity

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
