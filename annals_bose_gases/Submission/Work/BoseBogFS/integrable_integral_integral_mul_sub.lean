import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **Young/convolution fact in iterated-integral form**: for integrable `F H : ℝ³ → ℝ`, the
function `ν ↦ ∫ η, F η * H (ν - η)` is integrable and its integral is the product of the integrals:
  `∫ ν, ∫ η, F η * H (ν - η) = (∫ F) * (∫ H)`.
Hints (all in Mathlib, `open MeasureTheory`): `MeasureTheory.convolution_mul` (or `convolution_def`
plus `ContinuousLinearMap.mul_apply`) identifies `∫ η, F η * H (ν - η)` with
`MeasureTheory.convolution F H (ContinuousLinearMap.mul ℝ ℝ) ν` (the scalar multiplication as a
continuous bilinear map); then `MeasureTheory.Integrable.integrable_convolution` and
`MeasureTheory.integral_convolution` (both with `μ = ν = volume`, `G = EuclideanSpace ℝ (Fin 3)`,
the ambient Haar measure `volume` being `IsAddRightInvariant` and `SFinite`) give the two conjuncts,
with `ContinuousLinearMap.mul_apply` turning `(L a) b` into `a * b`. -/
theorem integrable_integral_integral_mul_sub {F H : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : MeasureTheory.Integrable F) (hH : MeasureTheory.Integrable H) :
    MeasureTheory.Integrable (fun ν : EuclideanSpace ℝ (Fin 3) =>
        ∫ η : EuclideanSpace ℝ (Fin 3), F η * H (ν - η))
      ∧ (∫ ν : EuclideanSpace ℝ (Fin 3), ∫ η : EuclideanSpace ℝ (Fin 3), F η * H (ν - η))
          = (∫ η : EuclideanSpace ℝ (Fin 3), F η) * (∫ ν : EuclideanSpace ℝ (Fin 3), H ν) := by
  have hfun : (fun ν : EuclideanSpace ℝ (Fin 3) =>
        ∫ η : EuclideanSpace ℝ (Fin 3), F η * H (ν - η))
      = MeasureTheory.convolution F H (ContinuousLinearMap.mul ℝ ℝ) := by
    funext ν
    rw [MeasureTheory.convolution_mul]
  rw [hfun]
  refine ⟨hF.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hH, ?_⟩
  rw [MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hF hH]
  simp

end Work.BoseBogFS
