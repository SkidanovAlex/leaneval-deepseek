import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Calculus

open MeasureTheory Set

theorem intervalIntegrable_of_continuousOn_Ioo_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Ioo a b)) (hbdd : ∀ x ∈ Set.Ioo a b, |f x| ≤ C) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hIoo_ae : Set.Ioo a b =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Set.Ioc a b :=
    Ioo_ae_eq_Ioc
  have hmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have h : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [Measure.restrict_congr_set hIoo_ae] at h
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)), ‖f x‖ ≤ C := by
    have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)), x ∈ Set.Ioo a b := by
      have h : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo a b)), x ∈ Set.Ioo a b :=
        ae_restrict_mem measurableSet_Ioo
      rwa [Measure.restrict_congr_set hIoo_ae] at h
    exact hae.mono (fun x hx => by simpa [Real.norm_eq_abs] using hbdd x hx)
  have hfin : MeasureTheory.volume (Set.Ioc a b) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hint : IntegrableOn f (Set.Ioc a b) MeasureTheory.volume :=
    IntegrableOn.of_bound hfin hmeas C hbound
  refine ⟨hint, ?_⟩
  have hnil : Set.Ioc b a = ∅ := by
    rw [Set.Ioc_eq_empty_iff]
    exact not_lt.mpr hab
  rw [hnil]
  exact integrableOn_empty

end Commons.Analysis.Calculus