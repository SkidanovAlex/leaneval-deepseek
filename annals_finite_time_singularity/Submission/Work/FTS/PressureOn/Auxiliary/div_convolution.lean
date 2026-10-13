import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

-- The divergence commutes with convolution with a locally integrable kernel `ρ`:
-- for `f : ℝ³ → ℝ³` of class `C¹` with compact support,
-- `div (ρ ⋆ f) x = (ρ ⋆ div f) x` for every `x`.
--
-- Proof.  `HasCompactSupport.hasFDerivAt_convolution_right` differentiates the convolution in the
-- second argument, so `fderiv ℝ (ρ ⋆ f) x = (ρ ⋆[L.precompR ℝ³] fderiv ℝ f) x`.  The trace of an
-- endomorphism of `ℝ³` is the sum of the diagonal entries in the standard basis
-- (`trace_eq_sum_single`), and `convolution_precompR_apply` evaluates the precompR-convolution at
-- each basis vector as a scalar convolution.  Coordinate extraction from the Bochner integral is
-- `eval_integral_piLp` (integrability of the integrands is `ConvolutionExists` for the compactly
-- supported functions `y ↦ fderiv ℝ f y (e i)`, which is `HasCompactSupport.fderiv_apply`), and
-- the sum of the diagonal entries is `div f` by `div_eq_sum_single`.
theorem div_convolution (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : MeasureTheory.LocallyIntegrable ρ MeasureTheory.volume)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∀ x, FiniteTimeSingularity.div
        (fun y => MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y) x
      = MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
  intro x
  have hFcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hFcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  -- Differentiate the convolution in the second argument.
  have hderiv : HasFDerivAt
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
      (MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x) x :=
    hfc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ hf x
  change (fderiv ℝ
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) x).trace ℝ R3
      = MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
  rw [hderiv.fderiv, Work.FTS.PressureOn.trace_eq_sum_single]
  -- `convolution_precompR_apply`: value of the derivative on a vector.
  have hpre : ∀ v : R3,
      (MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x) v
      = MeasureTheory.convolution ρ (fun a => fderiv ℝ f a v)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := fun v =>
    MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ
      hFcs hFcont x v
  -- Integrability of the (compactly supported) integrands, in vector and in coordinate form.
  have hVint : ∀ i : Fin 3,
      MeasureTheory.Integrable
        (fun t : R3 => ρ t • (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ))))) := by
    intro i
    have hGcont : Continuous
        (fun y : R3 => fderiv ℝ f y (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      hFcont.clm_apply continuous_const
    have hGcs : HasCompactSupport
        (fun y : R3 => fderiv ℝ f y (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      hfc.fderiv_apply ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ)))
    exact hGcs.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ hGcont x
  have hcoordint : ∀ i j : Fin 3, MeasureTheory.Integrable
      (fun t : R3 => ρ t *
        (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp j) :=
    fun i j => by simpa [PiLp.smul_apply] using (hVint i).eval_piLp j
  -- The `i`-th diagonal entry of the derivative, as a scalar convolution.
  have hcoord : ∀ i : Fin 3,
      ((MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x)
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp i
      = ∫ t : R3, ρ t *
          (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp i := by
    intro i
    rw [hpre]
    rw [show MeasureTheory.convolution ρ
          (fun a => fderiv ℝ f a (WithLp.toLp 2 (Pi.single i (1 : ℝ))))
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : R3, ρ t •
            (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) from rfl]
    rw [MeasureTheory.eval_integral_piLp
      (f := fun t : R3 => ρ t •
        (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))))
      (fun j => by simpa [PiLp.smul_apply] using (hVint i).eval_piLp j) i]
    simp [PiLp.smul_apply]
  -- The right-hand side, as an integral.
  have hdiv : MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
      = ∫ t : R3, ρ t * FiniteTimeSingularity.div f (x - t) := by
    rw [show MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : R3, ρ t • FiniteTimeSingularity.div f (x - t) from rfl]
    simp
  rw [hdiv, Finset.sum_congr rfl (fun i _ => hcoord i)]
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hcoordint i i)]
  congr 1
  funext t
  rw [← Finset.mul_sum, ← Work.FTS.PressureOn.div_eq_sum_single]

end Work.FTS.PressureOn.Auxiliary
