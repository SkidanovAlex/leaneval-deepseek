import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ψ · div ω` is integrable for compactly supported `ψ ∈ C¹` and locally integrable `Dω`

`Work.FTS.PressureOn.integrable_mul_div`: if `ω : ℝ³ → ℝ³` has *locally integrable* Jacobian
`Dω : ℝ³ → (ℝ³ →L[ℝ] ℝ³)` and `ψ : ℝ³ → ℝ` is `C¹` with compact support, then
`y ↦ ψ y * div ω y` is integrable.

This is the integrability input of the pressure reconstruction: the pressure potential is defined
by convolving the Lamb vector with the Newtonian kernel and multiplying by a cutoff `ψ`; the only
measure-theoretic ingredient is that a compactly supported continuous function times a locally
integrable function is integrable (Mathlib's
`MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`), applied to the
divergence `div ω = trace (Dω)`.  The divergence inherits local integrability from `Dω` because
`div ω = ∑ᵢ (Dω · eᵢ)ᵢ` is a finite sum of compositions of `Dω` with the continuous linear maps
`L ↦ (L eᵢ)ᵢ` (`ContinuousLinearMap.locallyIntegrableOn_comp`).

The trace-in-the-standard-basis identity `div_eq_sum_single` is taken from the sibling module
`Submission/Work/FTS/PressureOn/integral_div_eq_zero_of_hasFDerivAt.lean`.
-/

open MeasureTheory Filter

namespace Work.FTS.PressureOn

/-- The `i`-th diagonal entry of the Jacobian, `y ↦ (Dω y)(eᵢ)ᵢ`, is locally integrable whenever
`Dω` is: it is the composite of `Dω` with the continuous linear map `L ↦ (L eᵢ)ᵢ`, the
composition of the evaluation `L ↦ L eᵢ` with the coordinate projection `PiLp.proj`. -/
lemma locallyIntegrable_diag (ω : R3 → R3)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) (i : Fin 3) :
    MeasureTheory.LocallyIntegrable (fun y : R3 =>
      (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i) := by
  set v : R3 := WithLp.toLp 2 (Pi.single i (1 : ℝ)) with hv
  set hL : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.apply ℝ R3 v) with hLdef
  have key : (fun y : R3 => (fderiv ℝ ω y) v i)
      = ⇑hL ∘ (fun x => fderiv ℝ ω x) := by
    funext y
    simp only [Function.comp_apply, hLdef, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.apply_apply, PiLp.proj_apply]
  rw [key]
  exact MeasureTheory.locallyIntegrableOn_univ.mp
    (hL.locallyIntegrableOn_comp (MeasureTheory.locallyIntegrableOn_univ.mpr hωint))

/-- The diagonal-part sum `y ↦ ∑ᵢ (Dω y)(eᵢ)ᵢ = div ω y` is locally integrable whenever `Dω`
is: a finite sum of the locally integrable diagonal entries (Mathlib's
`MeasureTheory.locallyIntegrable_finsetSum`), rewritten with the trace identity
`div_eq_sum_single`. -/
lemma locallyIntegrable_div (ω : R3 → R3)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) :
    MeasureTheory.LocallyIntegrable (fun y : R3 => FiniteTimeSingularity.div ω y) := by
  have hsum : MeasureTheory.LocallyIntegrable (fun y : R3 =>
      ∑ i : Fin 3, (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i) :=
    MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun i y => (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i)
      (fun i _ => locallyIntegrable_diag ω hωint i)
  refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (div_eq_sum_single ω y).symm

theorem integrable_mul_div {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {ψ : Work.FTS.PressureOn.R3 → ℝ}
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun y => ψ y * FiniteTimeSingularity.div ω y) := by
  have h := (locallyIntegrable_div ω hωint).integrable_smul_left_of_hasCompactSupport
    hψ.continuous hψcs
  simpa only [smul_eq_mul] using h

end Work.FTS.PressureOn
