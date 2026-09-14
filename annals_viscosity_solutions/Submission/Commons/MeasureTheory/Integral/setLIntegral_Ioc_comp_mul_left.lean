import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory Set
open scoped ENNReal

/-- Change of variables `s = a * t` for the Lebesgue integral over a half-open interval:
for `a > 0`, `∫⁻ t in Ioc b c, F (a * t) = a⁻¹ * ∫⁻ s in Ioc (a*b) (a*c), F s`.

Suggested route: `MeasureTheory.Measure.map` with `Real.map_volume_mul_left`
(`Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume`), `Measure.restrict_map`
(the map `a * ·` is injective on `Ioc b c`) and `(a * ·) '' Ioc b c = Ioc (a * b) (a * c)` for
`a > 0`, together with `lintegral_map` / the definition of `setLIntegral`. -/
theorem setLIntegral_Ioc_comp_mul_left (F : ℝ → ℝ≥0∞) {a b c : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioc b c, F (a * t) = ENNReal.ofReal a⁻¹ * ∫⁻ s in Set.Ioc (a * b) (a * c), F s := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have ha_inv_pos : 0 < a⁻¹ := inv_pos.mpr ha
  set e : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ a ha_ne with he
  have he_coe : ⇑e = (a * ·) := by rw [he]; exact MeasurableEquiv.coe_mulLeft₀ ha_ne
  have himg : e '' Set.Ioc b c = Set.Ioc (a * b) (a * c) := by
    rw [he_coe]; exact image_mul_left_Ioc ha b c
  have hpre : e ⁻¹' Set.Ioc (a * b) (a * c) = Set.Ioc b c := by
    rw [← himg, Set.preimage_image_eq _ e.injective]
  have hmap : Measure.map e volume = ENNReal.ofReal a⁻¹ • volume := by
    rw [he_coe, Real.map_volume_mul_left ha_ne, abs_of_pos ha_inv_pos]
  have hres : Measure.map e (volume.restrict (Set.Ioc b c))
      = (Measure.map e volume).restrict (Set.Ioc (a * b) (a * c)) := by
    have h1 := Measure.restrict_map (μ := volume) (f := ⇑e) e.measurable
      (s := Set.Ioc (a * b) (a * c)) measurableSet_Ioc
    rw [hpre] at h1
    exact h1.symm
  calc
    ∫⁻ t in Set.Ioc b c, F (a * t)
        = ∫⁻ t, F (e t) ∂(volume.restrict (Set.Ioc b c)) := by rw [he_coe]
    _ = ∫⁻ s, F s ∂(Measure.map e (volume.restrict (Set.Ioc b c))) := by
          rw [lintegral_map_equiv F e]
    _ = ∫⁻ s, F s ∂((Measure.map e volume).restrict (Set.Ioc (a * b) (a * c))) := by
          rw [hres]
    _ = ∫⁻ s, F s ∂((ENNReal.ofReal a⁻¹ • volume).restrict (Set.Ioc (a * b) (a * c))) := by
          rw [hmap]
    _ = ∫⁻ s, F s ∂(ENNReal.ofReal a⁻¹ • volume.restrict (Set.Ioc (a * b) (a * c))) := by
          rw [Measure.restrict_smul]
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ s in Set.Ioc (a * b) (a * c), F s := by
          rw [lintegral_smul_measure, smul_eq_mul]

end Commons.MeasureTheory.Integral