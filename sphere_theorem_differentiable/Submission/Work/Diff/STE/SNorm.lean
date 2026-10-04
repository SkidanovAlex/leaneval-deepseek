import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.ChartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B: the chartwise-Fourier Sobolev norm `‖·‖ₖ` of a metric (design `B3`)

Fix a finite atlas `x₀ : ι₀ → M` with a subordinate smooth partition of unity `θ`
(`exists_smoothPartition_ball_cover`).  The norm of a smooth metric `g` is the sum, over the charts
and the component pairs `(a,b)`, of the Layer A norms `CSq k` of the Fourier coefficients of the
*periodisation* of the flat representative `flatRep θ x₀ g i a b` (whose support is inside a chart
ball, hence — after shrinking the radii — inside the half-open unit cube, exactly the hypothesis of
`periodization_contDiff_periodic`).

This file only *defines* the norm; the estimates (finiteness, the transfer of the Layer A product,
Moser, Gårding and mollifier estimates, and the comparison with the chartwise sup norms) are the
next Layer B obligations.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Work.Diff.STE

/-- The periodic representative of a chartwise localised component: the periodisation (sum over the
lattice `ℤⁿ`) of the flat representative `flatRep`. -/
noncomputable def perComp {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (g : SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun x => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((flatRep θ x₀ g i a b (x + fun j => (m j : ℝ))) : ℂ)

/-- The chartwise-Fourier Sobolev norm `‖g‖ₖ` of Layer B. -/
noncomputable def SNorm {ι₀ : Type*} [Fintype ι₀] (θ : SmoothPartitionOfUnity ι₀ I M)
    (x₀ : ι₀ → M) (k : ℕ) (g : SMet I M) : ℝ :=
  ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    CSq k (fourierCoeff (perComp θ x₀ g i a b))

end Work.Diff.STE

end
