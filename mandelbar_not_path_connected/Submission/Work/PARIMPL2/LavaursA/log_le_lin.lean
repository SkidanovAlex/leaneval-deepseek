import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.LavaursA

/-- **`C log (a + b R)` is dominated by `c R`.**  For `C ≥ 0`, `b > 0`, `c > 0` the function `R ↦ C * Real.log (a + b * R)` is eventually dominated by the linear function `R ↦ c * R` (the content is `log = o(id)` at `+∞`; the affine argument is harmless). -/
theorem log_le_lin (C a b c : ℝ) (hC : 0 ≤ C) (hb : 0 < b) (hc : 0 < c) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → C * Real.log (a + b * R) ≤ c * R := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- the degenerate case `C = 0`: the left-hand side vanishes
    refine ⟨1, one_pos, fun R hR => ?_⟩
    rw [← hC0, zero_mul]
    exact mul_nonneg (le_of_lt hc) (by linarith)
  · -- `C > 0`: compare `log` with a suitable small multiple of its argument
    set k : ℝ := c / (2 * C * b) with hkdef
    have hk : 0 < k := by rw [hkdef]; positivity
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have hbne : b ≠ 0 := ne_of_gt hb
    have hcne : c ≠ 0 := ne_of_gt hc
    -- the slope produced by `log x ≤ k x` is exactly `c / (2 * C)`
    have hCkb : C * k * b = c / 2 := by
      rw [hkdef]
      field_simp
    -- `log = o(id)` at `+∞`, hence `log x ≤ k x` eventually
    have hlog : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ k * x := by
      have h1 := Real.isLittleO_log_id_atTop.def hk
      filter_upwards [h1, Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
      simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hx0] at hx
      exact (le_abs_self _).trans hx
    -- the affine argument tends to `+∞`
    have htend : Filter.Tendsto (fun R : ℝ => a + b * R) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left Filter.atTop a
        (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id)
    have hcomp : ∀ᶠ R : ℝ in Filter.atTop, Real.log (a + b * R) ≤ k * (a + b * R) :=
      htend.eventually hlog
    have hfin : ∀ᶠ R : ℝ in Filter.atTop, C * Real.log (a + b * R) ≤ c * R := by
      filter_upwards [hcomp, Filter.eventually_ge_atTop (2 * C * k * a / c)] with R hcompR hR
      -- the constant term `C * k * a` is swallowed by half of `c * R`
      have hbound : C * k * a ≤ (c / 2) * R := by
        have h1 : (2 * C * k * a / c) * c ≤ R * c := mul_le_mul_of_nonneg_right hR (le_of_lt hc)
        have h2 : (2 * C * k * a / c) * c = 2 * (C * k * a) := by
          field_simp
        linarith
      have hstep1 : C * Real.log (a + b * R) ≤ C * (k * (a + b * R)) :=
        mul_le_mul_of_nonneg_left hcompR (le_of_lt hCpos)
      have hstep2 : C * (k * (a + b * R)) = C * k * a + (c / 2) * R := by
        rw [← hCkb]; ring
      linarith
    obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1 hfin
    exact ⟨max 1 R₁, lt_of_lt_of_le one_pos (le_max_left _ _),
      fun R hR => hR₁ R (le_trans (le_max_right _ _) hR)⟩

end Work.PARIMPL2.LavaursA
