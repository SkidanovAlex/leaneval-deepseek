import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

/-- For any real `C`, for all sufficiently large `t` the logarithmic expression
`C * (log t + 2 * π)` is bounded by `t / 2`. -/
theorem exists_threshold_log_div (C : ℝ) : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → C * (Real.log t + 2 * Real.pi) ≤ t / 2 := by
  -- `log t / t → 0` as `t → ∞`
  have hlog : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  -- hence `C * (log t + 2π) / t → 0`
  have hlim : Filter.Tendsto
      (fun t : ℝ => C * (Real.log t / t) + (2 * Real.pi * C) * t⁻¹) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => C * (Real.log t / t)) Filter.atTop (nhds (C * 0)) :=
      hlog.const_mul C
    have h2 : Filter.Tendsto (fun t : ℝ => (2 * Real.pi * C) * t⁻¹) Filter.atTop
        (nhds ((2 * Real.pi * C) * 0)) :=
      tendsto_inv_atTop_zero.const_mul (2 * Real.pi * C)
    have := h1.add h2
    simpa using this
  -- so eventually it is below `1 / 2`
  have hev : ∀ᶠ t in Filter.atTop,
      C * (Real.log t / t) + (2 * Real.pi * C) * t⁻¹ < 1 / 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  rcases Filter.eventually_atTop.1 hev with ⟨a, ha⟩
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have h := ha t (le_trans (le_max_left _ _) ht)
  have hrewrite :
      C * (Real.log t / t) + (2 * Real.pi * C) * t⁻¹ = C * (Real.log t + 2 * Real.pi) / t := by
    field_simp
  rw [hrewrite] at h
  have h2 := (div_lt_iff₀ ht0).1 h
  linarith

end Work.FatouCoord.Flower
