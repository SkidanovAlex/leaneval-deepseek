import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.PARIMPL2.Lavaurs

/-- **The eventual bound `C (1 + log R) ≤ 3R/4`.**  For every `C ≥ 0` there is `R₀ ≥ 1` with
`C (1 + log R) ≤ 3R/4` for all `R ≥ R₀`.  Equivalent to the vanishing of `C/R + C log R / R` at
`+∞` (`Real.isLittleO_log_id_atTop`, or the `log R / R → 0` limit).

This is the real-analysis ingredient of the *reachability* condition of the transit
(`Work.PARIMPL2.Lavaurs.transit_model`, `Work.PARIMPL2.RchOK'`): the level `Re Ũ = R` of the
perturbed Écalle cylinder is reached by the model orbit only if `‖κ‖ log R ≲ R`. -/
theorem exists_log_mul_le (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R ≥ R₀, C * (1 + Real.log R) ≤ 3 * R / 4 := by
  have hg : Filter.Tendsto (fun R : ℝ => Real.log R / R) Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hf : Filter.Tendsto (fun R : ℝ => C * (1 + Real.log R) / R) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => C / R) Filter.atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id C
    have h2 : Filter.Tendsto (fun R : ℝ => C * (Real.log R / R)) Filter.atTop (𝓝 0) := by
      simpa using hg.const_mul C
    have hsum : Filter.Tendsto (fun R : ℝ => C / R + C * (Real.log R / R))
        Filter.atTop (𝓝 0) := by
      simpa using h1.add h2
    refine hsum.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with R hR
    field_simp
  have hb : ∀ᶠ R in Filter.atTop, C * (1 + Real.log R) / R ≤ 3 / 4 :=
    hf.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 3 / 4))
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 1 a, le_max_left _ _, ?_⟩
  intro R hR
  have ha' : a ≤ R := le_trans (le_max_right _ _) hR
  have h1R : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos h1R
  have hbound := ha R ha'
  have heq : C * (1 + Real.log R) = (C * (1 + Real.log R) / R) * R := by
    field_simp
  rw [heq]
  calc (C * (1 + Real.log R) / R) * R ≤ (3 / 4) * R :=
        mul_le_mul_of_nonneg_right hbound hRpos.le
    _ = 3 * R / 4 := by ring

end Work.PARIMPL2.Lavaurs
