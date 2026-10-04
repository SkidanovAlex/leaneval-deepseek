import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.STE.ChartComp
import Submission.Work.Diff.STE.SNorm
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B2: the chartwise components of a section of `Sym² T*M`

Layer D of the STE design runs a Galerkin scheme for an unknown **section of `Sym² T*M`** (a family
of bilinear forms, the metric being `g₀ + h`).  The analytic norms are read off from the chartwise
components of that section, i.e. from the *chart matrices* of the bilinear forms — the same objects
as `Work.Diff.STE.chartComp` for a metric, but for an arbitrary section.

This file provides:

* `Bil` — the type of pointwise bilinear forms on the tangent bundle;
* `bilChart`, `bilChartFlat` — the chart matrix of a section in the coordinate frame of a chart,
  as a function on `E`, resp. on the flat coordinates `Fin n → ℝ` centred at the chart centre;
* `bilLoc`, `bilFlat` — the localised (cut off by a family of functions `χ i`) and
  centre-translated representative;
* `bilPer` — its periodisation, a `1`-periodic `ℂ`-valued function of the flat coordinates (this is
  what Layer A's Fourier theory applies to);
* `BNorm` — the *composite* norm `Σ_i Σ_{ab} CSq k (fourierCoeff (R_i h)_{ab})`.

The smoothness and periodicity of `bilPer` (given a cut-off whose support lies in the cube, and
smoothness of the chart matrix on the chart target) is `contDiff_perComp_of_bump` transported from
`SMet` to `Bil`; the pointwise control `|h| ≤ Σ_i sup |χ i · bilChart|` and the gauge formula
relating the chart matrices of two charts are the two remaining Layer B2 obligations (see
`DESIGN.md`, SESSION 6, §3).
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Sections of `Sym² T*M`**: pointwise bilinear forms on the tangent bundle.  A smooth metric
`g` is the special case `fun x => g.inner x`. -/
abbrev Bil := Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/-- The affine identification of the flat coordinates centred at the chart centre with the model
space `E` (the analogue of `Work.Diff.STE.aff` for a single chart). -/
def flatToE (x₀ : M) : (Fin (Module.finrank ℝ E) → ℝ) → E :=
  fun z => (Module.finBasis ℝ E).equivFun.symm
    ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z)

@[simp] lemma flatToE_apply (x₀ : M) (z : Fin (Module.finrank ℝ E) → ℝ) :
    flatToE (I := I) x₀ z = (Module.finBasis ℝ E).equivFun.symm
      ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) := rfl

/-- **The chart matrix of a section** in the coordinate frame of the chart at `x₀`, as a function
of the model space `E` (generalises `Work.Diff.STE.chartComp` from `SMet` to `Bil`). -/
def bilChart (h : Bil (I := I) (M := M)) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => h ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector x₀ ((extChartAt I x₀).symm y) (Module.finBasis ℝ E a))
    (Submission.Geodesic.frameVector x₀ ((extChartAt I x₀).symm y) (Module.finBasis ℝ E b))

/-- The chart matrix read in the flat coordinates centred at the chart centre. -/
def bilChartFlat (h : Bil (I := I) (M := M)) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z => bilChart h x₀ a b (flatToE (I := I) x₀ z)

/-- The localised component of a section: the chart matrix in the chart of `x₀` multiplied by a
cut-off `χ` (in the design, a bump which is `1` on a ball covering `M` and supported in a slightly
larger ball inside the chart target and inside the unit cube). -/
def bilLoc {ι₀ : Type*} (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (x₀ : ι₀ → M)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z => χ i z * bilChartFlat h (x₀ i) a b z

/-- The periodisation of the localised component: a `1`-periodic `ℂ`-valued function of the flat
coordinates, to which the whole of Layer A applies.  This is the component map `R_i` of the design
(denoted `R_α` in `DESIGN.md`, §B2). -/
def bilPer {ι₀ : Type*} (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (x₀ : ι₀ → M)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun z => ∑' m : Fin (Module.finrank ℝ E) → ℤ,
    ((bilLoc χ x₀ h i a b (z + iVec m) : ℝ) : ℂ)

/-- **The composite norm** of a section: the sum of the Layer A norms `CSq k` of the Fourier
coefficients of its localised, periodised chart components. -/
def BNorm {ι₀ : Type*} [Fintype ι₀] (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (x₀ : ι₀ → M) (k : ℕ) (h : Bil (I := I) (M := M)) : ℝ :=
  ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    CSq k (fourierCoeff (bilPer χ x₀ h i a b))

/-- **The composite pairing** of two sections, used as the `L²` pairing of the energy method: the
sum of the (complex) `L²` pairings of the localised, periodised chart components. -/
def BPair {ι₀ : Type*} [Fintype ι₀] (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (x₀ : ι₀ → M) (h k : Bil (I := I) (M := M)) : ℂ :=
  ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    L2IP (bilPer χ x₀ h i a b) (bilPer χ x₀ k i a b)

/-- The chart matrix of a metric, read as the chart matrix of the section `fun x => g.inner x`: this
is `rfl` and identifies the Layer B2 vocabulary with the already proved `ChartComp.chartComp`. -/
lemma chartComp_eq_bilChart (g : Submission.Diff.SMet I M) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartComp g x₀ a b = bilChart (I := I) (M := M) (fun x => g.inner x) x₀ a b := rfl

end Work.Diff.STE
