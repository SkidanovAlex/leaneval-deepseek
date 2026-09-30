import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter

namespace Commons.Analysis.Calculus

/-- Asymptotic expansion at `0⁺`: if `w t * t → 1`, then
`(w t - cot t) * t^2 → 0`.  This is the `K = 1` Riccati/Sturm comparison
asymptotic, obtained from `sin t ~ t`, `cos t → 1`. -/
theorem tendsto_cot_asymptotic_of_mul_tendsto_one {w : ℝ → ℝ}
    (hw : Filter.Tendsto (fun t => w t * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    Filter.Tendsto (fun t => (w t - Real.cot t) * t ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hl : nhdsWithin 0 (Set.Ioi 0) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
  -- `cos t → 1`
  have hcos : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := (Real.continuous_cos.tendsto 0).mono_left hl
    simpa [Real.cos_zero] using h
  -- `t → 0`
  have hid : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (Filter.tendsto_id (α := ℝ) (x := nhdsWithin 0 (Set.Ioi 0))).mono_right hl
  -- `sin t / t → 1`
  have hsin_div : Tendsto (fun t : ℝ => Real.sin t / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Tendsto Real.sinc (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h := (Real.continuous_sinc.tendsto 0).mono_left hl
      simpa [Real.sinc_zero] using h
    refine Filter.Tendsto.congr' ?_ h1
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sinc_of_ne_zero (ne_of_gt ht)
  -- `t / sin t → 1`
  have ht_div_sin : Tendsto (fun t : ℝ => t / Real.sin t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := hsin_div.inv₀ (one_ne_zero)
    simpa [inv_div] using h
  -- `w t * sin t → 1`
  have hws : Tendsto (fun t : ℝ => w t * Real.sin t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := hw.mul hsin_div
    rw [one_mul] at h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with t
    by_cases ht : t = 0
    · subst ht; simp
    · field_simp
  -- `w t * sin t - cos t → 0`
  have hA : Tendsto (fun t : ℝ => w t * Real.sin t - Real.cos t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hws.sub hcos
    simpa using h
  -- `t * (t / sin t) → 0`
  have hB : Tendsto (fun t : ℝ => t * (t / Real.sin t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hid.mul ht_div_sin
    simpa using h
  have hAB : Tendsto (fun t : ℝ => (w t * Real.sin t - Real.cos t) * (t * (t / Real.sin t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hA.mul hB
    simpa using h
  -- eventual equality of the two expressions
  have hlt : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), t < Real.pi := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds Real.pi_pos] with t ht _
    exact ht
  have hsin_ne : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), Real.sin t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht hlt'
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht hlt')
  have heq : (fun t : ℝ => (w t * Real.sin t - Real.cos t) * (t * (t / Real.sin t)))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => (w t - Real.cot t) * t ^ 2) := by
    filter_upwards [hsin_ne] with t ht
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  exact Filter.Tendsto.congr' heq hAB

end Commons.Analysis.Calculus