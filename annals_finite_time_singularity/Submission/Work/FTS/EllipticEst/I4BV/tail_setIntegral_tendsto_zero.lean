import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.I4BV

/-- **Tail integrals of an integrable function vanish.**  If `g` is integrable on
`(a, b)` then `t ↦ ∫ x in (t, b), g x` tends to `0` as `t → b` from below.

This is the absolute continuity of the set integral `s ↦ ∫_s g` combined with
`volume (t, b) → 0`: replace `g` by its extension by `0` off `(a, b)` (integrable
on `ℝ`) and note that for `t > a` the two set integrals over `(t, b)` coincide.
The measure of `(t, b)` is `ofReal (b - t)`, which tends to `0`. -/
theorem tail_setIntegral_tendsto_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo a b)) :
    Filter.Tendsto (fun t => ∫ x in Set.Ioo t b, g x)
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
  -- the extension of `g` by `0` off `(a, b)` is integrable on `ℝ`
  have hf : MeasureTheory.Integrable ((Set.Ioo a b).indicator g) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2 hg
  -- `volume (Ioo t b) → 0` as `t → b⁻`
  have hs : Filter.Tendsto (fun t => MeasureTheory.volume (Set.Ioo t b))
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
    have hbt : Filter.Tendsto (fun t : ℝ => b - t) (nhdsWithin b (Set.Iio b)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ => b - t) (nhds b) (nhds (b - b)) :=
        (continuous_const.sub continuous_id).tendsto b
      simpa using h1.mono_left nhdsWithin_le_nhds
    have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp hbt
    simpa [Function.comp_def, Real.volume_Ioo] using h3
  -- absolute continuity of the set integral
  have hmain := hf.tendsto_setIntegral_nhds_zero hs
  -- for `t > a` the two set integrals over `(t, b)` agree
  refine Filter.Tendsto.congr' ?_ hmain
  have hev : ∀ᶠ t in nhdsWithin b (Set.Iio b), a < t :=
    (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with t ht
  have hsub : Set.Ioo t b ⊆ Set.Ioo a b := fun x hx => ⟨lt_trans ht hx.1, hx.2⟩
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo, Set.inter_eq_left.mpr hsub]

end Work.FTS.EllipticEst.I4BV
