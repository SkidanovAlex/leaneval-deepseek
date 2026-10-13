import Mathlib
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval

namespace Work.WilE5.Flat
open WilkiesDesign WilkiesDesign.E

/-!
## Strict differentiability of `eaEval`

`eaEval c Q : (Fin k → ℝ) → ℝ` is the evaluation of the EA-polynomial `Q` at
`(x, exp (ℓ_j x))`; it is a `C^1` (indeed real analytic) function, and
`Work.WilE5.Calc.hasFDerivAt_eaEval` computes its Fréchet derivative as the
linear form `Work.WilE5.Calc.eaEvalD c Q x = ∑ i, eaEval c (eaD c i Q) x • proj i`.

Here we upgrade this to a *strict* Fréchet derivative.  The route is the Mathlib
criterion `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`: a function which has a
Fréchet derivative everywhere near `x` and whose derivative depends continuously on the
base point is strictly differentiable at `x`.  Both inputs are available:

* `Work.WilE5.Calc.hasFDerivAt_eaEval c Q y` is the Fréchet derivative at every point `y`,
  with derivative `eaEvalD c Q y`;
* `y ↦ eaEvalD c Q y` is continuous, because it is a finite sum of the continuous scalar
  functions `y ↦ eaEval c (eaD c i Q) y` times the constant projections.  Each of those
  scalar functions is continuous by `HasFDerivAt.continuousAt`, applied to
  `Work.WilE5.Calc.hasFDerivAt_eaEval`.
-/

/-- `eaEval c Q` is a continuous function of the base point. -/
theorem continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous (fun z : Fin k → ℝ => eaEval c Q z) :=
  continuous_iff_continuousAt.mpr fun z =>
    (Work.WilE5.Calc.hasFDerivAt_eaEval c Q z).continuousAt

/-- The Fréchet derivative `eaEvalD c Q` of `eaEval c Q` is continuous in the base point. -/
theorem continuous_eaEvalD {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous (fun z : Fin k → ℝ => Work.WilE5.Calc.eaEvalD c Q z) := by
  simp only [Work.WilE5.Calc.eaEvalD]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_eaEval c (eaD c i Q)).smul continuous_const

/-- `eaEval c Q` is strictly differentiable, with the same derivative as the Fréchet derivative
computed in `Submission.Work.WilE5.Calc.hasFDerivAt_eaEval` (it is `C^1`, indeed real analytic).
Route: `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` (Mathlib, `Analysis/Calculus/MeanValue`)
applied to `Work.WilE5.Calc.hasFDerivAt_eaEval c Q`, whose derivative
`z ↦ ∑ i, eaEval c (eaD c i Q) z • proj i` is continuous in `z` (its components are `eaEval`'s,
which are continuous by `HasFDerivAt.continuousAt`); alternatively real analyticity of `eaEval`. -/
theorem strictFDeriv_eaEval {k r : ℕ} (c : EAChain k r)
    (Q : EAPoly k r) (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => eaEval c Q z)
      ((∑ i : Fin k, (eaEval c (eaD c i Q) x) • ContinuousLinearMap.proj i) :
        (Fin k → ℝ) →L[ℝ] ℝ) x := by
  have h := hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (𝕜 := ℝ) (x := x)
    (f := fun z : Fin k → ℝ => eaEval c Q z)
    (f' := fun y : Fin k → ℝ => Work.WilE5.Calc.eaEvalD c Q y)
    (Filter.Eventually.of_forall fun y => by
      simpa only [Work.WilE5.Calc.eaEvalD] using Work.WilE5.Calc.hasFDerivAt_eaEval c Q y)
    (continuous_eaEvalD c Q).continuousAt
  simpa only [Work.WilE5.Calc.eaEvalD] using h

end Work.WilE5.Flat

/-! The same statement under the doubly nested namespace `Work.WilE5.Flat.Work.WilE5.Flat`,
kept as a compatibility alias for files of this area which were set up that way. -/
namespace Work.WilE5.Flat

namespace Work.WilE5.Flat
open WilkiesDesign WilkiesDesign.E

set_option linter.dupNamespace false in
/-- Compatibility alias of `Work.WilE5.Flat.strictFDeriv_eaEval`. -/
theorem strictFDeriv_eaEval {k r : ℕ} (c : EAChain k r)
    (Q : EAPoly k r) (x : Fin k → ℝ) :
    HasStrictFDerivAt (fun z : Fin k → ℝ => eaEval c Q z)
      ((∑ i : Fin k, (eaEval c (eaD c i Q) x) • ContinuousLinearMap.proj i) :
        (Fin k → ℝ) →L[ℝ] ℝ) x :=
  _root_.Work.WilE5.Flat.strictFDeriv_eaEval c Q x

end Work.WilE5.Flat

end Work.WilE5.Flat
