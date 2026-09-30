/-
# Smooth global fields agreeing with the chart frame near a point

The chart frame fields `frameVector x₀ p u` (or rather the sections `frameSection x₀ u`) are
smooth *on the chart*, but not globally: `frameSection` is defined by junk values outside the
chart.  `Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection` produces,
for every `u : E` and every point `x₀` of the chart source, a *globally* `C^∞` section agreeing with
`frameSection x₀ u` near `x₀`.  This file fixes such a choice once and for all as
`smoothFrameField x₀ u`, so that downstream statements can quantify over the basis vectors of `E`
instead of carrying existential choices around.

The choice is `Classical.choose` of the existence statement at the point `x₀` itself.
-/
import Submission.Work.LeviCivita.Defs
import Submission.Work.RiemLib.ChartConnection

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- A **globally smooth section** of the tangent bundle which agrees with the chart frame field
`frameSection x₀ u` in a neighbourhood of `x₀`. -/
noncomputable def smoothFrameField (x₀ : M) (u : E) : Π x : M, TangentSpace I x :=
  Classical.choose (Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
    (I := I) x₀ u (mem_chart_source H x₀))

/-- `smoothFrameField x₀ u` is a `C^∞` section. -/
lemma smoothFrameField_contMDiff (x₀ : M) (u : E) :
    ContMDiff I I.tangent ∞ (T% (smoothFrameField (I := I) x₀ u)) :=
  (Classical.choose_spec
    (Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
      (I := I) x₀ u (mem_chart_source H x₀))).1

/-- `smoothFrameField x₀ u` agrees with `frameSection x₀ u` near `x₀`. -/
lemma smoothFrameField_eventuallyEq (x₀ : M) (u : E) :
    smoothFrameField (I := I) x₀ u =ᶠ[𝓝 x₀] frameSection (I := I) x₀ u :=
  (Classical.choose_spec
    (Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
      (I := I) x₀ u (mem_chart_source H x₀))).2

end

end Work.LeviCivita
