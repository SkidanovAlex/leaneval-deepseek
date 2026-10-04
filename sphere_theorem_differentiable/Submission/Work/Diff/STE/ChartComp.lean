import Mathlib
import Submission.Diff.Interfaces
import Submission.Geodesic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B, first step: the chartwise components of a metric

This file starts the "components" construction of the design (`B2`): for a smooth metric
`g : SMet I M` and a chart at `x₀`, the functions

* `chartComp g x₀ a b : E → ℝ`, `y ↦ g(∂_a, ∂_b)` at the point of `M` with chart coordinates `y`
  (the coordinate vector `∂_a` being the trivialisation-constant field `frameVector x₀ · b_a`),
* `chartCompFlat g x₀ a b : (Fin n → ℝ) → ℝ`, the same read in coordinates `E ≃ ℝⁿ` via the basis
  `Module.finBasis ℝ E` — these are the flat functions to which Layer A's Fourier theory applies.

The next steps (see `DESIGN.md`) are: smoothness of `chartComp` on the chart target, the
localisation with a bump function, the periodisation (`periodization_contDiff_periodic`,
`pd_periodization` — already proved), the norm `‖h‖ₖ`, and the mollifier `J_ε`.
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

/-- The components of a metric `g` in the chart at `x₀`, as a function on the chart's model space
`E` (the coordinate `y` is identified with the point `(extChartAt I x₀).symm y` of `M`). -/
noncomputable def chartComp (g : SMet I M) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => g.inner ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector x₀ ((extChartAt I x₀).symm y) (Module.finBasis ℝ E a))
    (Submission.Geodesic.frameVector x₀ ((extChartAt I x₀).symm y) (Module.finBasis ℝ E b))

/-- The chart components of `g` read as a function of the coordinates `Fin n → ℝ` through the
basis identification `E ≃ ℝⁿ`; this is the flat function to which Layer A applies. -/
noncomputable def chartCompFlat (g : SMet I M) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun x => chartComp g x₀ a b ((Module.finBasis ℝ E).equivFun.symm x)

/-- The components of a metric in the chart of the `i`-th element of a finite atlas, localised
with a smooth partition of unity `θ` (the design's `B2`: `θ_α · (h(e_a,e_b))`). -/
noncomputable def locComp {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (g : SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => θ i ((extChartAt I (x₀ i)).symm y) * chartComp g (x₀ i) a b y

/-- The chartwise localised component of a metric, read in the flat coordinates `Fin n → ℝ` and
translated to the origin (so that its support lies near `0` and the periodisation of Layer A
applies).  This is the flat function whose `CSq`-norms define the Sobolev norms `‖·‖ₖ` of Layer B;
its support-smallness is `support_locComp_subset` composed with the translation. -/
noncomputable def flatRep {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (g : SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun x => locComp (I := I) θ x₀ g i a b ((Module.finBasis ℝ E).equivFun.symm
    ((Module.finBasis ℝ E).equivFun ((extChartAt I (x₀ i)) (x₀ i)) + x))

end Work.Diff.STE

end
