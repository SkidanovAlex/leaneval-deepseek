import Mathlib
import Submission.Port.Aesm

namespace Work.KMTAreas.SupNorm

open MeasureTheory

/-- Change of variables for the `ℒᵖ` seminorm of a dilation `x ↦ H (c * x)` of a function
`H : ℝ → ℂ` with respect to Lebesgue measure on `ℝ`, `0 < c`: the dilation scales the seminorm
by `(c⁻¹)^{1/p}`. -/
theorem eLpNorm_comp_mul_left_eq (H : ℝ → ℂ) {c : ℝ} (hc : 0 < c) {p : ENNReal} (hpt : p ≠ ⊤)
    (hH : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume := by pw_aesm) :
    MeasureTheory.eLpNorm (fun x => H (c * x)) p MeasureTheory.volume
      = ENNReal.ofReal c⁻¹ ^ (1 / p).toReal * MeasureTheory.eLpNorm H p MeasureTheory.volume := by
  have hcne : c ≠ 0 := ne_of_gt hc
  -- Lebesgue measure pushed forward by `x ↦ c * x` is `c⁻¹ • volume`.
  have hmap : MeasureTheory.Measure.map (fun x : ℝ => c * x) MeasureTheory.volume
      = ENNReal.ofReal c⁻¹ • MeasureTheory.volume := by
    have h := MeasureTheory.Measure.map_addHaar_smul (μ := (MeasureTheory.volume : Measure ℝ))
      (E := ℝ) hcne
    simpa [abs_of_nonneg (inv_nonneg.mpr hc.le), Module.finrank_self] using h
  -- Pull the dilation inside the seminorm: `‖H ∘ (c * ·)‖_p = ‖H‖_p` w.r.t. the pushed measure.
  have h : MeasureTheory.eLpNorm H p (MeasureTheory.Measure.map (fun x : ℝ => c * x)
        MeasureTheory.volume)
      = MeasureTheory.eLpNorm (fun x => H (c * x)) p MeasureTheory.volume :=
    (measurableEmbedding_mulLeft₀ hcne).eLpNorm_map_measure
  rw [← h, hmap, MeasureTheory.eLpNorm_smul_measure_of_ne_top (hf := hH) hpt H (ENNReal.ofReal c⁻¹)]
  simp

end Work.KMTAreas.SupNorm
