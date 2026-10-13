/-
Work module: the *packaged* single-slice hypothesis of
`Work.FTS.EllipticEst.Honest.I4GlobalAssembly`.

`I4GlobalAssembly` takes, as a hypothesis, the (analytic, non-trivial) single-slice inequality
of the honest `I₄` upper bound.  That hypothesis is a long `∀ Φ, … → … → … → …` statement, and
this module gives it a name so that the auxiliary lemmas about it can be stated without copying
the whole term.  `SliceIneq` is a *verbatim* copy of the type written in `I4GlobalAssembly`, so
`hS : SliceIneq := hslice` is a definitional unfolding.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.Honest

/-- **The single-slice inequality of the honest `I₄` upper bound** (hypothesis of
`I4GlobalAssembly`): for every `Φ : ℝ → ℝ` of class `C²` on `(0, π/2)` whose weighted squares
`∫_θ (Φ/cos θ)²σ` and `∫_θ (Φ'')²σ` are integrable (`σ = sin(2θ)^{-η}`, `η = 99/100`),

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ (Φ/cos θ)²σ + √(∫_θ(Φ/cos θ)²σ)·√(∫_θ(Φ'')²σ)`. -/
def SliceIneq : Prop :=
  ∀ (Φ : ℝ → ℝ), ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      (∫ θ in Set.Icc 0 (Real.pi / 2),
          deriv (fun θ' => Real.tan θ' * Φ θ') θ * deriv (deriv Φ) θ
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        ≤ 50 * (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          + Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
            * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))

end Work.FTS.EllipticEst.Honest
