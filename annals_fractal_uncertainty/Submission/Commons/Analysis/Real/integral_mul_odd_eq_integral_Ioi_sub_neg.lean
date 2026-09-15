import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Commons.Analysis.Real

open MeasureTheory Set

theorem integral_mul_odd_eq_integral_Ioi_sub_neg (f w : ℝ → ℝ)
    (hw : ∀ x : ℝ, w (-x) = -w x)
    (hf : MeasureTheory.Integrable (fun x : ℝ => f x * w x)) :
    MeasureTheory.integral MeasureTheory.volume (fun x : ℝ => f x * w x)
      = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun u => (f u - f (-u)) * w u) := by
  let g : ℝ → ℝ := fun x => f x * w x
  have hg_int : MeasureTheory.Integrable g MeasureTheory.volume := hf
  have hg_Iio : MeasureTheory.IntegrableOn g (Set.Iio 0) MeasureTheory.volume :=
    hg_int.integrableOn.mono_set Set.Iio_subset_Iic_self
  have hgneg_Ioi :
      MeasureTheory.IntegrableOn (fun x => g (-x)) (Set.Ioi 0) MeasureTheory.volume := by
    have h := hg_Iio.comp_neg
    simpa using h
  have hg_Ioi : MeasureTheory.IntegrableOn g (Set.Ioi 0) MeasureTheory.volume :=
    hg_int.integrableOn
  have hsplit :
      (∫ x in Set.Iic (0 : ℝ), g x) + (∫ x in Set.Ioi (0 : ℝ), g x)
        = ∫ x, g x := by
    simpa using MeasureTheory.integral_add_compl (μ := MeasureTheory.volume)
      (s := Set.Iic (0 : ℝ)) measurableSet_Iic hg_int
  have hIic_eq :
      (∫ x in Set.Iic (0 : ℝ), g x) = ∫ x in Set.Ioi (0 : ℝ), g (-x) := by
    simp
  have hpt : ∀ x : ℝ, (f x - f (-x)) * w x = g x + g (-x) := by
    intro x
    simp only [g]
    rw [hw x]
    ring
  calc
    (∫ x, g x)
        = (∫ x in Set.Iic (0 : ℝ), g x) + (∫ x in Set.Ioi (0 : ℝ), g x) :=
          hsplit.symm
    _ = (∫ x in Set.Ioi (0 : ℝ), g (-x)) + (∫ x in Set.Ioi (0 : ℝ), g x) := by
          rw [hIic_eq]
    _ = ∫ x in Set.Ioi (0 : ℝ), (g (-x) + g x) :=
          (MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            hgneg_Ioi hg_Ioi).symm
    _ = ∫ x in Set.Ioi (0 : ℝ), (f x - f (-x)) * w x := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by
            show g (-x) + g x = (f x - f (-x)) * w x
            rw [hpt x]; ring)

end Commons.Analysis.Real