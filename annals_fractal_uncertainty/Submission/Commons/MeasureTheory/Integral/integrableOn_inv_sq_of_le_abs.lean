import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Set

namespace Commons.MeasureTheory.Integral

theorem integrableOn_inv_sq_of_le_abs {δ : ℝ} (hδ : 0 < δ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) {t : ℝ | δ ≤ |t|} volume := by
  have hpow : ∀ x : ℝ, 0 < x → x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    intro x hx
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx), Real.rpow_two]
  have hIoi : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi δ) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hδ).congr_fun
      (fun x hx => hpow x (hδ.trans hx)) measurableSet_Ioi
  have hIio : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Iio (-δ)) volume := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
        (Measure.measurePreserving_neg (volume : Measure ℝ))
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hIoi
    simpa [Function.comp_def] using h
  have hIci : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ici δ) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => (t ^ 2)⁻¹) (b := δ)).mpr hIoi
  have hIic : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Iic (-δ)) volume :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := fun t : ℝ => (t ^ 2)⁻¹) (b := -δ)).mpr hIio
  convert hIic.union hIci using 1
  ext t
  simp [mem_Iic, mem_Ici, le_abs, le_neg, or_comm]

end Commons.MeasureTheory.Integral