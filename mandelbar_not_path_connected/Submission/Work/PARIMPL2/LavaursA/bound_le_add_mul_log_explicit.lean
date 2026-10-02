import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.LavaursA

/-- **The log-domination bound, with an explicit constant.**  For `c ≥ 0` every `t > 0` satisfying `t ≤ D + c log t` is bounded by the explicit expression `max 1 (4 (2 + c + |D| + c²)²)`.  (Derivation: for `t ≥ 1`, `log t = 2 log √t ≤ 2√t − 2`, so `u := √t` satisfies `(u − c)² ≤ D + c² − 2c`; hence `u ≤ c + √(D + c² − 2c) ≤ 2 + c + |D| + c²` whenever `D + c² − 2c ≥ 0`, and there is no `t > 1` solution otherwise.) -/
theorem bound_le_add_mul_log_explicit {c D : ℝ} (hc : 0 ≤ c) :
    ∀ t : ℝ, 0 < t → t ≤ D + c * Real.log t → t ≤ max 1 (4 * (2 + c + |D| + c ^ 2) ^ 2) := by
  intro t ht hle
  -- Put `M := 2 + c + |D| + c²`, the explicit constant inside the bound.
  set M : ℝ := 2 + c + |D| + c ^ 2 with hM
  have hM_ge_c : c ≤ M := by rw [hM]; nlinarith [abs_nonneg D]
  have hM_ge1 : 1 ≤ M := by rw [hM]; nlinarith [abs_nonneg D, sq_nonneg c, hc]
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM_ge1
  -- `u := √t > 0`, `u² = t`.
  set u : ℝ := Real.sqrt t with hu
  have hu_pos : 0 < u := by rw [hu]; exact Real.sqrt_pos.mpr ht
  have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
  have hu_sq : u ^ 2 = t := by rw [hu]; exact Real.sq_sqrt (le_of_lt ht)
  -- `log t = 2 log u ≤ 2u − 2`.
  have hlog : Real.log t = 2 * Real.log u := by
    rw [← hu_sq, Real.log_pow]
    norm_num
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
  -- Therefore `t ≤ D + c (2u − 2)`.
  have hstep : t ≤ D + c * (2 * u - 2) := by
    have h2 : c * Real.log t ≤ c * (2 * u - 2) := by
      rw [hlog]
      exact mul_le_mul_of_nonneg_left (by linarith) hc
    linarith
  -- Squaring up: `(u − c)² ≤ c² − 2c + D`.
  have hquad : (u - c) ^ 2 ≤ c ^ 2 - 2 * c + D := by
    have hh : u ^ 2 ≤ D + c * (2 * u - 2) := by rw [hu_sq]; exact hstep
    nlinarith [hh]
  -- And `c² − 2c + D ≤ M²`.
  have hMD : c ^ 2 - 2 * c + D ≤ M ^ 2 := by
    have h_le1 : c ^ 2 - 2 * c + D ≤ c ^ 2 + |D| := by nlinarith [hc, le_abs_self D]
    have h_le2 : c ^ 2 + |D| ≤ M := by rw [hM]; nlinarith [hc]
    have h_le3 : M ≤ M ^ 2 := by nlinarith [hM_ge1]
    linarith
  have hsquare : (u - c) ^ 2 ≤ M ^ 2 := le_trans hquad hMD
  -- Hence `u − c ≤ M`, i.e. `u ≤ M + c ≤ 2M`.
  have hu_le : u ≤ M + c := by
    have h1 : u - c ≤ Real.sqrt ((u - c) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    have h2 : Real.sqrt ((u - c) ^ 2) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hsquare
    have h3 : Real.sqrt (M ^ 2) = M := Real.sqrt_sq hM_nonneg
    linarith
  have hu_le2 : u ≤ 2 * M := by linarith [hM_ge_c]
  -- So `t = u² ≤ (2M)² = 4M² ≤ max 1 (4M²)`.
  have ht_le : t ≤ 4 * M ^ 2 := by
    rw [← hu_sq]
    nlinarith [hu_le2, hu_nonneg, hM_nonneg]
  rw [hM] at ht_le
  exact le_trans ht_le (le_max_right 1 _)

end Work.PARIMPL2.LavaursA
