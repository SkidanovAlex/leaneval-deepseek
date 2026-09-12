import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

theorem log_geom_decay_steps {a b : ℝ} (h0b : 0 < b) (hba : b < a) (ha1 : a < 1)
    {n ℓ u : ℕ} (hnpos : 0 < (n : ℝ)) (hℓge : (n : ℝ) ≤ 2 * (ℓ : ℝ))
    (hpow : a ^ ℓ < b ^ u) :
    ((ℓ : ℝ) - (u : ℝ)) > (n : ℝ) * Real.log (a / b) / (2 * (-Real.log b)) := by
  let L : ℝ := (ℓ : ℝ)
  let U : ℝ := (u : ℝ)
  let N : ℝ := (n : ℝ)
  let D : ℝ := Real.log (a / b)
  let α : ℝ := -Real.log b
  have h0a : 0 < a := lt_trans h0b hba
  have hb1 : b < 1 := lt_trans hba ha1
  have hb_ne : b ≠ 0 := ne_of_gt h0b
  have ha_ne : a ≠ 0 := ne_of_gt h0a
  have hlogb_neg : Real.log b < 0 := Real.log_neg h0b hb1
  have hloga_neg : Real.log a < 0 := Real.log_neg h0a ha1
  have hD_eq : D = Real.log a - Real.log b := by
    dsimp [D]
    rw [Real.log_div ha_ne hb_ne]
  have hD_pos : 0 < D := by
    rw [hD_eq]
    linarith [Real.log_lt_log h0b hba]
  have hα_pos : 0 < α := by
    dsimp [α]
    linarith
  have hlogb_eq : Real.log b = -α := by dsimp [α]; ring
  have hloga_eq : Real.log a = D - α := by
    rw [hD_eq]
    dsimp [α]
    ring
  -- take log of the power inequality
  have hpowpos_a : 0 < a ^ ℓ := pow_pos h0a ℓ
  have hlog_pow_lt : Real.log (a ^ ℓ) < Real.log (b ^ u) :=
    Real.log_lt_log hpowpos_a hpow
  have hlog' : L * Real.log a < U * Real.log b := by
    simp only [Real.log_pow] at hlog_pow_lt
    simpa [L, U] using hlog_pow_lt
  have hlog'' : L * (D - α) < U * (-α) := by
    rw [hloga_eq, hlogb_eq] at hlog'
    simpa using hlog'
  have hmain : L * D < (L - U) * α := by nlinarith
  -- now use ℓ ≥ n / 2
  have hle : N ≤ 2 * L := by simpa [N, L] using hℓge
  have h2main : N * D < (L - U) * (2 * α) := by
    have hleft : 2 * L * D < (L - U) * (2 * α) := by nlinarith [hmain]
    have hright : N * D ≤ 2 * L * D := by
      exact mul_le_mul_of_nonneg_right hle (le_of_lt hD_pos)
    exact lt_of_le_of_lt hright hleft
  have hden : 0 < 2 * α := by nlinarith [hα_pos]
  have hfrac : N * D / (2 * α) < L - U := (div_lt_iff₀ hden).2 h2main
  simpa [L, U, N, D, α] using hfrac

end Commons.Analysis.Real