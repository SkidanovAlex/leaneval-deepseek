import Mathlib

namespace Work.HP.MDEstimates.hiparts

/-- For all sufficiently large `B`, the square of the logarithm of `192 B ^ 2` is bounded by
`B ^ (1/1000)`.  This is the elementary logarithmic-vs-polynomial comparison used to
control the `(log (4Δ))^2` factor appearing in the Hasse-principle estimates.  We take the
explicit threshold `B₁ = 10 ^ 20000`. -/
theorem log_sq_le : ∃ B₁ : ℝ, 1 ≤ B₁ ∧ ∀ A B Δ : ℝ, B₁ ≤ B → 1 ≤ A → 1 ≤ Δ → Δ ≤ 48 * B ^ 2 / A →
      (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1 : ℝ) / 1000) := by
  refine ⟨(10 : ℝ) ^ (20000 : ℕ), one_le_pow₀ (by norm_num), ?_⟩
  intro A B Δ hBB1 hA hΔ hΔle
  have hB : (1 : ℝ) ≤ B := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)) hBB1
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  -- Step 1: reduce `log (4 Δ)` to `log 192 + 2 log B`.
  have hΔle48 : Δ ≤ 48 * B ^ 2 := by
    have h1 : 48 * B ^ 2 / A ≤ 48 * B ^ 2 := by
      rw [div_le_iff₀ hApos]
      nlinarith [sq_nonneg B, hA]
    linarith
  have h4Δ : 4 * Δ ≤ 192 * B ^ 2 := by nlinarith [hΔle48]
  have hlog_le : Real.log (4 * Δ) ≤ Real.log 192 + 2 * Real.log B := by
    have h1 : Real.log (4 * Δ) ≤ Real.log (192 * B ^ 2) :=
      Real.log_le_log (by positivity) h4Δ
    have h2 : Real.log (192 * B ^ 2) = Real.log 192 + 2 * Real.log B := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt hBpos)), Real.log_pow]
      ring
    linarith [h1, h2]
  -- Step 2: substitute `u = B ^ (1/2000)`.
  set u : ℝ := B ^ ((1 : ℝ) / 2000) with hu_def
  have hu_pos : 0 < u := by rw [hu_def]; exact Real.rpow_pos_of_pos hBpos _
  have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
  have hlogB : Real.log B = 2000 * Real.log u := by
    rw [hu_def, Real.log_rpow hBpos]
    ring
  have hBpow : B ^ ((1 : ℝ) / 1000) = u ^ 2 := by
    rw [hu_def]
    rw [show (1 : ℝ) / 1000 = (1 : ℝ) / 2000 * 2 by norm_num]
    rw [Real.rpow_mul (le_of_lt hBpos)]
    rw [Real.rpow_two]
  have hu_large : ((10 : ℝ) ^ 5) ^ 2 ≤ u := by
    rw [hu_def]
    have h1 : ((10 : ℝ) ^ (20000 : ℕ)) ^ ((1 : ℝ) / 2000) ≤ B ^ ((1 : ℝ) / 2000) :=
      Real.rpow_le_rpow (by positivity) hBB1 (by norm_num)
    have h2 : ((10 : ℝ) ^ (20000 : ℕ)) ^ ((1 : ℝ) / 2000) = ((10 : ℝ) ^ 5) ^ 2 := by
      rw [← Real.rpow_natCast (10 : ℝ) 20000,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))]
      rw [show ((20000 : ℕ) : ℝ) * ((1 : ℝ) / 2000) = (10 : ℝ) by norm_num]
      norm_num
    calc ((10 : ℝ) ^ 5) ^ 2 = ((10 : ℝ) ^ (20000 : ℕ)) ^ ((1 : ℝ) / 2000) := h2.symm
      _ ≤ B ^ ((1 : ℝ) / 2000) := h1
  -- Step 3: the analytic core, `log 192 + 2 log B ≤ u / 2`.
  have hmain_le : Real.log 192 + 2 * Real.log B ≤ u / 2 := by
    have h1 : Real.log u ≤ 2 * Real.sqrt u := by
      have h := Real.log_le_rpow_div hu_nonneg (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [Real.sqrt_eq_rpow]
      linarith [h]
    have hsqrt_ge : (10 : ℝ) ^ 5 ≤ Real.sqrt u := by
      have h := Real.sqrt_le_sqrt hu_large
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 5)] at h
    have h2 : Real.log 192 ≤ u / 4 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 192 by norm_num)
      have h764 : (764 : ℝ) ≤ u := by
        have : (764 : ℝ) ≤ ((10 : ℝ) ^ 5) ^ 2 := by norm_num
        linarith
      linarith
    have h3 : 4000 * Real.log u ≤ u / 4 := by
      have h80 : 8000 * Real.sqrt u ≤ u / 4 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
        have hsq_u : u = Real.sqrt u * Real.sqrt u := by
          rw [← sq, Real.sq_sqrt hu_nonneg]
        nlinarith [hsqrt_ge, hsqrt_nonneg, hsq_u]
      nlinarith [h1, h80]
    linarith [h2, h3, hlogB]
  -- Step 4: assemble.
  have hlog4Δ_nonneg : 0 ≤ Real.log (4 * Δ) := Real.log_nonneg (by linarith)
  have hL_nonneg : 0 ≤ Real.log 192 + 2 * Real.log B := by
    have h1 : 0 ≤ Real.log 192 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log B := Real.log_nonneg hB
    linarith
  calc (Real.log (4 * Δ)) ^ 2
      ≤ (Real.log 192 + 2 * Real.log B) ^ 2 := pow_le_pow_left₀ hlog4Δ_nonneg hlog_le 2
    _ ≤ (u / 2) ^ 2 := pow_le_pow_left₀ hL_nonneg hmain_le 2
    _ ≤ u ^ 2 := by nlinarith [hu_pos]
    _ = B ^ ((1 : ℝ) / 1000) := hBpow.symm

end Work.HP.MDEstimates.hiparts
