import Mathlib
import Submission.Work.Drive.N2.HeightBasics
import Submission.Work.Drive.N2.ChartSplit
import Submission.Work.Drive.N2.CritParam
import Submission.Work.Projection.volume_image_criticalValues_eq_zero

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace in
/-- **The chartwise Sard step.** Let `F : ℝ² → ℝ⁵` be a chart representation which is smooth and
immersive on the open set `T`, and let `a ≠ b` be two coordinate indices such that the `(a,b)`-minor
`depProj a b ∘ F'(y)` is bijective for every `y ∈ T`. Then the set of directions `v` for which the
height function `y ↦ ⟪v, F y⟫` has a degenerate critical point in `T` is Lebesgue-null. -/
theorem volume_badSet_eq_zero (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (T : Set (EuclideanSpace ℝ (Fin 2))) (hT : IsOpen T)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F T)
    (hdiff : ∀ y ∈ T, DifferentiableAt ℝ F y)
    (himm : ∀ y ∈ T, Function.Injective (fderiv ℝ F y))
    (a b : Fin 5) (hab : a ≠ b)
    (hmin : ∀ y ∈ T, Function.Bijective (Work.Drive.N2.minor F a b y)) :
    MeasureTheory.volume (Work.Drive.N2.badSet F T) = 0 := by
  refine MeasureTheory.measure_mono_null
    (badSet_subset_critPhiT_image (F := F) (T := T) hT hdiff a b hab hmin) ?_
  refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero MeasureTheory.volume
    (f' := fun z => fderiv ℝ (critPhiT F a b) z) ?_ ?_
  · intro z hz
    exact ((differentiableAt_critPhiT (F := F) (T := T) (a := a) (b := b) hT hF hmin
      hz.1).hasFDerivAt).hasFDerivWithinAt
  · intro z hz
    exact det_fderiv_critPhiT_eq_zero (F := F) (T := T) (a := a) (b := b) hT hF hab hmin hz

end Work.Drive.N2
