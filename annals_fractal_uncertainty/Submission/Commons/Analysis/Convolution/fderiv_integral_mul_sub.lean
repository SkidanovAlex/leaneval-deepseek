import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Filter
open scoped Convolution Topology

namespace Commons.Analysis.Convolution

theorem fderiv_integral_mul_sub {d : ℕ} {u : (Fin d → ℂ) → ℂ} {k : (Fin d → ℂ) → ℝ}
    (hk : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) k) (hks : HasCompactSupport k)
    (hu : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :
    ∀ (z v : Fin d → ℂ),
      (fderiv ℝ (fun z => ∫ t, k (z - t) • u t
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) z) v
      = ∫ t, ((fderiv ℝ k (z - t)) v) • u t
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  intro z v
  let F : (Fin d → ℂ) → ℂ := fun z => ∫ t, k (z - t) • u t
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))
  change (fderiv ℝ F z) v = ∫ t, ((fderiv ℝ k (z - t)) v) • u t
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)
  have hk1 : ContDiff ℝ (1 : WithTop ℕ∞) k := hk.of_le (by simp)
  have hF_eq : MeasureTheory.convolution (𝕜 := ℝ) u k L
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = F := by
    funext x
    rw [MeasureTheory.convolution_def]
    simp only [F]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [L, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  have hderiv := hks.hasFDerivAt_convolution_right (L := L) hu hk1 z
  rw [hF_eq] at hderiv
  rw [hderiv.fderiv]
  have hcont : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  rw [convolution_precompR_apply (L := L) (f := u) (g := fderiv ℝ k)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      hu (hks.fderiv ℝ) hcont z v]
  rw [MeasureTheory.convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [L, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self]

end Commons.Analysis.Convolution