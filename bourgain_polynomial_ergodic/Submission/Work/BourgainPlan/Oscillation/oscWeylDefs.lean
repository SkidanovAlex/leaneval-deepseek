import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

/-!
# The abstract Fourier-multiplier operator on `ℤ`

Both operators that the oscillation inequality for the polynomial averages passes through --
`polyWeylOp` (the honest polynomial average) and `polyModelOp` (the major-arc model) -- are of the
form

`x ↦ ∫_0^1 m(θ) · (∑_{j ∈ s} g j e(j θ)) · e(-x θ) dθ`,

with `m` a bounded measurable multiplier on the circle.  This file introduces that operator as
`opMul m g s` and records that the two concrete operators are definitionally instances of it.
Everything the oscillation argument needs about `opMul` (linearity in the multiplier, the
Plancherel/`ℓ²` bound, the telescoping estimate for a family of multipliers) can then be stated
once and for all for `opMul`.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Oscillation

open Work.BourgainPlan.Maximal

noncomputable section

/-- The Fourier-multiplier operator with multiplier `m` applied to the finitely supported
sequence `g` (summed over the finite set `s`), evaluated at the integer point `x`. -/
def opMul (m : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, m θ *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

/-- `polyModelOp` is `opMul` with the conjugate major-arc model as multiplier. -/
lemma opMul_polyModelOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) :
    polyModelOp P g s N x
      = opMul (fun θ => starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ)/4) N θ)) g s x := rfl

/-- `polyWeylOp` is `opMul` with the conjugate Weyl kernel as multiplier. -/
lemma opMul_polyWeylOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) :
    polyWeylOp P g s N x
      = opMul (fun θ => starRingEnd ℂ (polyWeylKernel P N θ)) g s x := rfl

end

end Work.BourgainPlan.Oscillation
