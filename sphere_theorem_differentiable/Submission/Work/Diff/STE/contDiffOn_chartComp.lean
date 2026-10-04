import Mathlib
import Submission.Work.Diff.STE.ChartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart components of a metric

`Submission.Work.Diff.STE.chartComp g x₀ a b : E → ℝ` is the `(a,b)`-component of a smooth metric
`g` in the chart at `x₀`, `y ↦ g(∂_a, ∂_b)` at the point of `M` with chart coordinates `y`
(the coordinate frame vector `∂_a` being the trivialisation-constant field
`Submission.Geodesic.frameVector x₀ · (finBasis a)`).

The main result, `contDiffOn_chartComp`, is that `chartComp g x₀ a b` is `C^∞` on the target of
the chart `extChartAt I x₀`.  This is the first step of Layer B of the short-time-existence
design (see `DESIGN.md`): it is what allows the flat Fourier theory of Layer A to be applied to
the local representatives of a metric.

The proof is in two steps:

* `contMDiffOn_metricComp`: the function `q ↦ g.inner q (V q) (W q)` on `M` is smooth whenever
  `V`, `W` are the trivialisation-constant fields of a chart; this is
  `ContMDiffWithinAt.clm_bundle_apply₂` applied to the smoothness `g.contMDiff` of the metric
  (viewed as a section of the bundle of bilinear forms) and the smoothness of the constant
  coordinate fields;
* `contDiffOn_chartComp`: composition with the (smooth) inverse of the chart.

The only technical point is that the version of "the constant coordinate field is smooth"
available in the library, `Submission.Geodesic.contMDiffAt_frameSection`, carries a `T2Space M`
assumption (inherited from its section variables); the statement we need must not, so we redo its
short proof as `contMDiffAt_frameSection'`.  The remaining hypotheses (`RiemannianBundle`,
`IsContMDiffRiemannianBundle`) are likewise not needed here and are dropped.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section with constant coordinates `v` in the chart at `x₀` is smooth at every point of the
chart.  This is `Submission.Geodesic.contMDiffAt_frameSection` with the `T2Space M` (and
Riemannian-bundle) hypotheses removed, which is what the present file needs. -/
lemma contMDiffAt_frameSection' (x₀ : M) (v : E) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    ContMDiffAt I I.tangent ∞ (T% (Submission.Geodesic.frameSection (I := I) x₀ v)) x := by
  rw [Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I (M := M)) x₀) (by simpa using hx)]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I (M := M)) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show Submission.Geodesic.frameSection (I := I) x₀ v y
      = (trivializationAt E (TangentSpace I (M := M)) x₀).symmL ℝ y v from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I (M := M)) x₀)
    (R := ℝ) hy v]
  exact congrArg Prod.snd
    (((trivializationAt E (TangentSpace I (M := M)) x₀)).apply_mk_symm hy v)

/-- The metric evaluated on two trivialisation-constant fields of the chart at `x₀` is smooth on
the source of that chart. -/
lemma contMDiffOn_metricComp (g : Submission.Diff.SMet I M) (x₀ : M) (A B : E) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun q : M => g.inner q (Submission.Geodesic.frameVector (I := I) x₀ q A)
        (Submission.Geodesic.frameVector (I := I) x₀ q B))
      (chartAt H x₀).source := by
  intro x hx
  have hψ := (g.contMDiff (x := x)).contMDiffWithinAt (s := (chartAt H x₀).source)
  have hv := (contMDiffAt_frameSection' (I := I) x₀ A hx).contMDiffWithinAt
    (s := (chartAt H x₀).source)
  have hw := (contMDiffAt_frameSection' (I := I) x₀ B hx).contMDiffWithinAt
    (s := (chartAt H x₀).source)
  have h := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
  simp only [contMDiffWithinAt_totalSpace] at h
  exact h.2

theorem contDiffOn_chartComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x₀ : M) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.chartComp g x₀ a b)
      (extChartAt I x₀).target := by
  have key := contMDiffOn_metricComp (I := I) g x₀
    (Module.finBasis ℝ E a) (Module.finBasis ℝ E b)
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun q : M => g.inner q
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E a))
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E b)))
        ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    key.comp (contMDiffOn_extChartAt_symm (I := I) x₀ (n := ∞)) (fun y hy => by
      rw [← extChartAt_source (I := I) x₀]
      exact (extChartAt I x₀).map_target hy)
  exact hcomp.contDiffOn

end Work.Diff.STE
