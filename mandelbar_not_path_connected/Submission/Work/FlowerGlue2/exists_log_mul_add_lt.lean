import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- For fixed constants `G ≥ 0` and `E`, the function `R ↦ G * log R + E` is eventually
dominated by the linear function `R ↦ R / 2`. -/
theorem exists_log_mul_add_lt (G E : ℝ) (hG : 0 ≤ G) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ R ≥ N, G * Real.log R + E < R / 2 := by
  -- `log R / R → 0`, hence `G * (log R / R) → 0`.
  have hlog : Filter.Tendsto (fun R : ℝ => Real.log R / R) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  -- `G * (log R / R) + E * R⁻¹ → 0`
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      G * (Real.log R / R) + E * R⁻¹ < 1 / 2 := by
    have h1 : Filter.Tendsto (fun R : ℝ => G * (Real.log R / R)) Filter.atTop
        (nhds (G * 0)) := hlog.const_mul G
    have h2 : Filter.Tendsto (fun R : ℝ => E * R⁻¹) Filter.atTop (nhds (E * 0)) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul E
    have h3 := h1.add h2
    have h4 := h3.eventually
      (eventually_lt_nhds (show G * 0 + E * 0 < (1 : ℝ) / 2 by norm_num))
    simpa using h4
  have hev2 : ∀ᶠ R : ℝ in Filter.atTop,
      (1 : ℝ) ≤ R ∧ G * (Real.log R / R) + E * R⁻¹ < 1 / 2 :=
    (Filter.eventually_ge_atTop 1).and hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev2
  refine ⟨N, (hN N le_rfl).1, fun R hR => ?_⟩
  obtain ⟨hR1, hlt⟩ := hN R hR
  have hpos : 0 < R := by linarith
  -- multiply the eventual estimate by the positive factor `R`
  have hmul := mul_lt_mul_of_pos_right hlt hpos
  have hL : (G * (Real.log R / R) + E * R⁻¹) * R = G * Real.log R + E := by
    field_simp
  have hR2 : (1 / 2 : ℝ) * R = R / 2 := by ring
  rw [hL, hR2] at hmul
  exact hmul

end Work.FlowerGlue2
