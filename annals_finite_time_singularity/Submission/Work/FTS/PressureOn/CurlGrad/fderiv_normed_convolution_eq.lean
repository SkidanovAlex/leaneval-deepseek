import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The statement below uses the bare names `volume` and `Measure`; bring them into scope.
open MeasureTheory

namespace Work.FTS.PressureOn.CurlGrad

/-- **Differentiating a convolution with a normed bump function.**  For `ψ : ℝ³ → ℝ` of class
`C¹` with compact support and any bump function `ρ : ContDiffBump (0 : ℝ³)`, the Fréchet derivative
of the convolution `ρ.normed volume ⋆ ψ` is the convolution of `ρ.normed volume` with the
derivative of `ψ`:

`fderiv ℝ (ρ.normed volume ⋆ ψ) x v = ((ρ.normed volume) ⋆ (fun y => fderiv ℝ ψ y v)) x`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq`.

Proof hints: `HasCompactSupport.hasFDerivAt_convolution_right`
(`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) with `L := ContinuousLinearMap.lsmul ℝ ℝ`,
`f := ρ.normed volume` (locally integrable: it is a bump function times a constant) and `g := ψ`
(compact support and `ContDiff ℝ 1`), then `HasFDerivAt.fderiv`;
`MeasureTheory.convolution_precompR_apply` (`Mathlib/Analysis/Convolution.lean`) evaluates the
`ContinuousLinearMap.precompR`-convolution at `v` and turns it into the scalar convolution of
`fun y => fderiv ℝ ψ y v`; `MeasureTheory.convolution_def` unfolds the definition.  Note the
convolution is `MeasureTheory.convolution f g L μ = fun x => ∫ t, L (f t) (g (x - t)) ∂μ`, so the
scalar convolution here is `∫ t, ρ.normed volume t * (fderiv ℝ ψ (x - t) v) ∂volume`. -/
theorem fderiv_normed_convolution_eq {ρ : ContDiffBump (0 : Work.FTS.PressureOn.R3)}
    {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (x v : Work.FTS.PressureOn.R3) :
    fderiv ℝ (MeasureTheory.convolution (ρ.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) x v
      = MeasureTheory.convolution (ρ.normed volume) (fun y => fderiv ℝ ψ y v)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  -- `ρ.normed volume` is a constant multiple of the bump function `ρ`, hence locally integrable.
  have hρi : MeasureTheory.LocallyIntegrable (ρ.normed (volume : Measure Work.FTS.PressureOn.R3))
      volume := ρ.integrable_normed.locallyIntegrable
  -- Differentiate the convolution in the second argument (which is `C¹` with compact support).
  have hdiff := hψcs.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρi hψ x
  rw [hdiff.fderiv]
  -- Evaluate the `precompR`-convolution at `v`, turning it into the scalar convolution.
  exact MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hρi
    (hψcs.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) x v

end Work.FTS.PressureOn.CurlGrad
