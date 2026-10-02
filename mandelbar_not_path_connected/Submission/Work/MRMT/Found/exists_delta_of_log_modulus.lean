import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- For every `C ε > 0` there is a small `δ ∈ (0, 1/8]` such that
`2 * sqrt (C / log (1/δ)) + δ < 3 * ε / 4`. This just records that as `δ → 0⁺`
the quantity `2 * sqrt (C / log (1/δ)) + δ` tends to `0`. -/
theorem exists_delta_of_log_modulus {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ 2 * Real.sqrt (C / Real.log (1 / δ)) + δ < 3 * ε / 4 := by
  -- Target half-width `a = 3ε/16`; choose `1/δ = N` large enough that
  -- `N ≥ 8`, `N ≥ 1/a` and `log N ≥ M = C/a²` (so that `sqrt (C/log N) ≤ a`).
  set a : ℝ := 3 * ε / 16 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  set M : ℝ := C / a ^ 2 with hM_def
  have hMpos : 0 < M := by rw [hM_def]; positivity
  set N : ℝ := max 8 (max (1 / a) (Real.exp M)) with hN_def
  have hN8 : (8:ℝ) ≤ N := by rw [hN_def]; exact le_max_left _ _
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN8
  have hNa : 1 / a ≤ N := by
    rw [hN_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hNexp : Real.exp M ≤ N := by
    rw [hN_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨1 / N, by positivity, one_div_le_one_div_of_le (by norm_num) hN8, ?_⟩
  rw [one_div_one_div]
  -- `log N ≥ M`
  have hlog : M ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos M) hNexp
    rwa [Real.log_exp] at h
  -- `C / log N ≤ C / M = a²`
  have hle : C / Real.log N ≤ C / M := div_le_div_of_nonneg_left (le_of_lt hC) hMpos hlog
  have hCM : C / M = a ^ 2 := by
    rw [hM_def]
    field_simp
  have hsqrt_eq : Real.sqrt (C / M) = a := by
    rw [hCM, Real.sqrt_sq (le_of_lt ha_pos)]
  -- `2 * sqrt (C / log N) ≤ 2a`
  have h2 : 2 * Real.sqrt (C / Real.log N) ≤ 2 * a := by
    have := Real.sqrt_le_sqrt hle
    linarith
  -- `1/N ≤ a`
  have hdle : 1 / N ≤ a := by
    have := one_div_le_one_div_of_le (show (0:ℝ) < 1 / a by positivity) hNa
    simpa using this
  have hmain : 2 * a + a < 3 * ε / 4 := by
    rw [ha_def]; linarith
  linarith

end Work.MRMT.Found
