import Mathlib
import Submission.Work.FIArea3.JointCount.prod_apply_symm_null_measurable

namespace Work.FIArea3.JointCount

open MeasureTheory Set

/-- **Cavalieri / Fubini for a convex set in `ℂ`.**  The Lebesgue area of a convex set
`Z ⊆ ℂ` equals the integral over `y : ℝ` of the length of the horizontal fibre
`{x : ℝ | x + y·i ∈ Z}`.  The point is that convexity only makes `Z` *null* measurable
(with respect to the Haar measure on `ℂ`), so one needs the null-measurable form of
Fubini, `prod_apply_symm_null_measurable`. -/
theorem volume_eq_lintegral_fiber (Z : Set ℂ) (hZ : Convex ℝ Z) :
    MeasureTheory.volume Z = ∫⁻ y : ℝ, MeasureTheory.volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} := by
  have hZnm : NullMeasurableSet Z MeasureTheory.volume := hZ.nullMeasurableSet MeasureTheory.volume
  set s : Set (ℝ × ℝ) := {p : ℝ × ℝ | (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ Z} with hs_def
  have hs_eq : Complex.measurableEquivRealProd '' Z = s := by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    ext p
    rw [Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
    simp only [hs_def, Set.mem_ofPred_eq]
  have hnm : NullMeasurableSet s (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]
    have hpre : NullMeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' Z)
        (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
      hZnm.preimage (Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving)
    have hpre_eq : Complex.measurableEquivRealProd.symm ⁻¹' Z = s :=
      (MeasurableEquiv.image_eq_preimage_symm Complex.measurableEquivRealProd Z).symm.trans hs_eq
    rwa [hpre_eq] at hpre
  have hvol : MeasureTheory.volume Z = MeasureTheory.volume s := by
    have h1 : MeasureTheory.volume (Complex.measurableEquivRealProd '' Z) = MeasureTheory.volume Z := by
      rw [MeasurableEquiv.image_eq_preimage_symm]
      exact (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage hZnm
    rw [hs_eq] at h1
    exact h1.symm
  have key : MeasureTheory.volume s =
      ∫⁻ y : ℝ, MeasureTheory.volume {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ Z} := by
    have hfub := prod_apply_symm_null_measurable
      (μ := (MeasureTheory.volume : Measure ℝ)) (ν := (MeasureTheory.volume : Measure ℝ)) hnm
    rw [← Measure.volume_eq_prod ℝ ℝ] at hfub
    rw [hfub]
    apply lintegral_congr
    intro y
    rfl
  exact hvol.trans key

end Work.FIArea3.JointCount
