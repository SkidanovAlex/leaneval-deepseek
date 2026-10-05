import Mathlib
import Submission.Work.RPCore.Saddle.descent_defs

/-!
# Continuity of the descent data attached to a `C¹` function

The descent direction uses only the three numbers `cval L`, `g1 L`, `g2 L` attached to the
derivative `L = fderiv ℝ F z`.  Since each of `cval`, `g1`, `g2` is a continuous linear
functional of `L`, and `z ↦ fderiv ℝ F z` is continuous for a `C¹` function `F`, the whole
descent data depends continuously on `z`.
-/

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

/-- `cval` is continuous in the functional, being evaluation at the fixed vector `d0 k l 1`. -/
theorem continuous_cval {k l : ℕ} : Continuous (fun L : D k l →L[ℝ] ℝ => cval L) :=
  (ContinuousLinearMap.apply ℝ ℝ (d0 k l (1 : ℝ))).continuous

/-- `g1` is continuous in the functional: it is the Riesz vector of `L.comp (d1 k l)`, and
`L ↦ L.comp (d1 k l)` is continuous linear, as is `InnerProductSpace.toDual.symm`. -/
theorem continuous_g1 {k l : ℕ} : Continuous (fun L : D k l →L[ℝ] ℝ => g1 L) :=
  ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm.continuous).comp
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin k)) (D k l) ℝ).flip (d1 k l)).continuous

/-- `g2` is continuous in the functional, by the same argument as for `g1`. -/
theorem continuous_g2 {k l : ℕ} : Continuous (fun L : D k l →L[ℝ] ℝ => g2 L) :=
  ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin l))).symm.continuous).comp
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin l)) (D k l) ℝ).flip (d2 k l)).continuous

theorem descent_data_continuous {k l : ℕ} (F : D k l → ℝ) (hF : ContDiff ℝ 1 F) :
    Continuous fun z => (cval (fderiv ℝ F z), g1 (fderiv ℝ F z), g2 (fderiv ℝ F z)) := by
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  exact ((continuous_cval (k := k) (l := l)).prodMk
    ((continuous_g1 (k := k) (l := l)).prodMk (continuous_g2 (k := k) (l := l)))).comp hfd

end Work.RPCore.Saddle
