import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `laplaceTrace` is invariant under translations

The Laplace trace `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)` of a function on `ℝ³` is unchanged by
precomposing `φ` with a translation: with `φ = fun z => ψ (z + y)` the translated function attains
at `x` the same value of the trace that `ψ` attains at `x + y`.  This is the second-derivative
chain rule for the translation `z ↦ z + y` (whose Fréchet derivative is the identity), applied
twice.

The pointwise input is Mathlib's unconditional `fderiv_comp_add_right`
(`fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a)`), which holds for the *total* `fderiv`
without any differentiability hypothesis; the two rewrites therefore close the sum coordinatewise.
-/

namespace Work.FTS.PressureOn.PoissonAux.KI

theorem laplaceTrace_comp_add (ψ : R3 → ℝ) (hψ : ContDiff ℝ 2 ψ) (y x : R3) :
    laplaceTrace (fun z : R3 => ψ (z + y)) x = laplaceTrace ψ (x + y) := by
  rw [laplaceTrace, laplaceTrace]
  have _hψ : ContDiff ℝ 2 ψ := hψ
  refine Finset.sum_congr rfl fun i _ => ?_
  -- first derivative: `fderiv ℝ (fun z => ψ (z + y)) w = fderiv ℝ ψ (w + y)`
  have h1 : (fun w : R3 => fderiv ℝ (fun z : R3 => ψ (z + y)) w (FiniteTimeSingularity.e i))
      = fun w : R3 => fderiv ℝ ψ (w + y) (FiniteTimeSingularity.e i) := by
    funext w
    simp only [fderiv_comp_add_right]
  rw [h1]
  -- second derivative: differentiate the translated first-derivative field
  have h2 : fderiv ℝ (fun w : R3 => fderiv ℝ ψ (w + y) (FiniteTimeSingularity.e i)) x
      = fderiv ℝ (fun w : R3 => fderiv ℝ ψ w (FiniteTimeSingularity.e i)) (x + y) :=
    fderiv_comp_add_right
      (f := fun v : R3 => fderiv ℝ ψ v (FiniteTimeSingularity.e i)) (a := y)
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i)) h2

end Work.FTS.PressureOn.PoissonAux.KI
