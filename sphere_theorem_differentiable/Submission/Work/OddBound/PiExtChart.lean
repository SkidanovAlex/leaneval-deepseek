import Mathlib
import Submission.Work.OddBound.PolygonChart

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polygon space `Fin (N-1) → M` as a charted space on the *normed* model `Fin (N-1) → E`

The mountain pass (`Work.OddBound.mountainPass.exists_critical_index_le_one_manifold`) and the
index transfer (`Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex`) both need
the polygon space `P = Fin (N-1) → M` to be a **charted space whose model is a normed space**:
`HasNegDefPlane H' f z` differentiates the chart expression `f ∘ e.symm` twice, so the chart
codomain `H'` must carry a norm.

Mathlib's `piChartedSpace` gives `ChartedSpace (ModelPi (fun _ ↦ H)) P`, whose model is the product
of the *chart codomains* `H`, and `H` is only a topological space in this project.  The fix is to
use `E`-valued charts: the **extended chart** `extChartAt I x : M → E` (whose source is the chart
source and which is `I ∘ chartAt H x` as a function).  This module

* packages `extChartAt I x` as an `OpenPartialHomeomorph M E`, called `extChartHomeo`;
* turns `{extChartHomeo x | x : M}` into a `ChartedSpace E M` (`chartedSpaceExtChart`);
* applies `piChartedSpace` to obtain `ChartedSpace (Fin (N-1) → E) (Fin (N-1) → M)`, whose charts
  are the products `OpenPartialHomeomorph.pi (fun i ↦ extChartHomeo (x i))`.

Nothing here is registered as a global instance: `chartedSpaceExtChart` clashes with the given
`ChartedSpace H M` whenever `H` unifies with `E`, so it is a plain `def` to be introduced with
`letI` where needed.

The smoothness facts for this structure (both `IsManifold 𝓘(ℝ, E) ∞ M` for `chartedSpaceExtChart`
and its `Fin (N-1)`-product) are delegated separately; they rest on
`ContMDiffAt I 𝓘(ℝ,E) n (extChartAt I x)` and
`ContMDiffOn 𝓘(ℝ,E) I n (extChartAt I x).symm`
(`Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean`), composed through the mixed-model chain rule.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- **The extended chart `extChartAt I x`, as an open partial homeomorphism into the model
space `E`.**  Its underlying function is `I ∘ chartAt H x`; it exists because (with `I.Boundaryless`)
`I.toHomeomorph : H ≃ₜ E` is a homeomorphism. -/
noncomputable def extChartHomeo [I.Boundaryless] (x : M) : OpenPartialHomeomorph M E :=
  (chartAt H x).transHomeomorph I.toHomeomorph

@[simp] theorem extChartHomeo_coe [I.Boundaryless] (x : M) (m : M) :
    extChartHomeo (I := I) x m = I ((chartAt H x) m) := rfl

@[simp] theorem extChartHomeo_source [I.Boundaryless] (x : M) :
    (extChartHomeo (I := I) x).source = (chartAt H x).source := rfl

theorem mem_extChartHomeo_source [I.Boundaryless] (x : M) :
    x ∈ (extChartHomeo (I := I) x).source := mem_chart_source H x

/-- **The `E`-valued chart structure on `M`** given by the extended charts.  Not an instance (it
clashes with `ChartedSpace H M` when `H` unifies with `E`); introduce it with `letI`. -/
@[instance_reducible]
noncomputable def chartedSpaceExtChart [I.Boundaryless] : ChartedSpace E M where
  atlas := Set.range (extChartHomeo (I := I))
  chartAt := extChartHomeo (I := I)
  mem_chart_source := fun x => mem_extChartHomeo_source (I := I) x
  chart_mem_atlas := fun x => ⟨x, rfl⟩

@[simp] theorem chartedSpaceExtChart_chartAt [I.Boundaryless] (x : M) :
    @ChartedSpace.chartAt E _ M _ (chartedSpaceExtChart (I := I)) x = extChartHomeo (I := I) x :=
  rfl

/-- **The polygon space `Fin (N-1) → M` as a charted space on `Fin (N-1) → E`**, obtained as the
finite product of `chartedSpaceExtChart`.  Not an instance; introduce it with `letI`. -/
@[instance_reducible]
noncomputable def piChartedSpaceExt [I.Boundaryless] (N : ℕ) :
    ChartedSpace ((Fin (N - 1)) → E) ((Fin (N - 1)) → M) :=
  @piChartedSpace (Fin (N - 1)) _ (fun _ => E) (fun _ => inferInstance)
    (fun _ => M) (fun _ => inferInstance) (fun _ => chartedSpaceExtChart (I := I))

/-- **The product of the extended charts at the vertices of the polygon `x`**: the explicit chart of
`piChartedSpaceExt` at `x`. -/
noncomputable def piExtChart [I.Boundaryless] {N : ℕ} (x : Fin (N - 1) → M) :
    OpenPartialHomeomorph (Fin (N - 1) → M) ((Fin (N - 1)) → E) :=
  OpenPartialHomeomorph.pi fun i => extChartHomeo (I := I) (x i)

@[simp] theorem piChartedSpaceExt_chartAt [I.Boundaryless] {N : ℕ} (x : Fin (N - 1) → M) :
    @ChartedSpace.chartAt ((Fin (N - 1)) → E) _ ((Fin (N - 1)) → M) _
      (piChartedSpaceExt (I := I) N) x = piExtChart (I := I) x :=
  rfl

theorem piExtChart_mem_atlas [I.Boundaryless] {N : ℕ} (x : Fin (N - 1) → M) :
    piExtChart (I := I) x ∈ @atlas ((Fin (N - 1)) → E) _ ((Fin (N - 1)) → M) _
      (piChartedSpaceExt (I := I) N) :=
  @chart_mem_atlas ((Fin (N - 1)) → E) ((Fin (N - 1)) → M) _ _
    (piChartedSpaceExt (I := I) N) x

theorem mem_piExtChart_source [I.Boundaryless] {N : ℕ} (x : Fin (N - 1) → M) :
    x ∈ (piExtChart (I := I) x).source :=
  @mem_chart_source ((Fin (N - 1)) → E) ((Fin (N - 1)) → M) _ _
    (piChartedSpaceExt (I := I) N) x

end

end Work.OddBound
