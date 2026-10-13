/-
# `Work.StabilityFar.St4Refine` — `St4` from *vorticity-level* hypotheses

`Work.StabilityFar.st4_farField_holder` takes the three far-field a priori estimates of the two
blocks of `fderiv u.uncurry` as hypotheses (`FarDerivLipschitz`, and the `t`-Hölder constants of
`Dₓu` and `∂ₜu`).  This module *derives* all three from the vorticity data, so that the far-field
`C^{1,α}` conclusion depends only on

* the smoothness of the solution near the window, and `u(·,t) = BS(ω(·,t))`,
  `∂ₜu(·,t) = BS(∂ₜω(·,t))`;
* the support, the `L^∞` bounds and the measurability of `ω` and `∂ₜω`;
* the `α`-Hölder-in-time regularity of `ω` and of `∂ₜω` on the support ball.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.FarDerivLipschitz
import Submission.Work.StabilityFar.Decay.fderiv_timeHolder
import Submission.Work.StabilityFar.Decay.timeDeriv_timeHolder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- **`St4` from the vorticity data.**  The three far-field a priori estimates used by
`st4_farField_holder` are produced by `farDerivLipschitz_of_biotSavart`,
`Decay.fderiv_timeHolder` and `Decay.timeDeriv_timeHolder`. -/
theorem st4_farField_holder_of_vorticity
    {α : NNReal} {ω u : R3 → ℝ → R3} {T R M M₁ H H₁ : ℝ}
    (hT : 0 < T) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hR : 0 < R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁)
    (hsmooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo (-1) (T + 1)))
    (hbs : IsBiotSavartSlice u ω T) (hbsDt : IsTimeBiotSavartSlice u ω T)
    (hsupp : SlicesSupported ω R T) (hbdd : SlicesBounded ω M T) (hmeas : SlicesMeasurable ω T)
    (hbddDt : SlicesBounded (timeDeriv ω) M₁ T) (hmeasDt : SlicesMeasurable (timeDeriv ω) T)
    (hth : TimeHolderOnBall (α : ℝ) ω R T H)
    (hthDt : TimeHolderOnBall (α : ℝ) (timeDeriv ω) R T H₁) :
    IsContDiffHolderOn ℝ α u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) := by
  obtain ⟨A, hA, hlip⟩ := farDerivLipschitz_of_biotSavart hR hM hbs hbdd hsupp hmeas
  obtain ⟨At, hAt, hatH⟩ := Decay.fderiv_timeHolder hR hM hH hα hbs hbdd hsupp hmeas hth
  obtain ⟨Atu, hAtu, hatuH⟩ :=
    Decay.timeDeriv_timeHolder hR hM₁ hH₁ hα hbsDt hbddDt hsupp hmeasDt hthDt
  exact st4_farField_holder hT hα hα1 hR hM hM₁ hH hH₁ hA hAt hAtu hsmooth hbs hbsDt hsupp hbdd
    hbddDt hmeasDt hth hthDt hlip hatH hatuH

end Work.StabilityFar
