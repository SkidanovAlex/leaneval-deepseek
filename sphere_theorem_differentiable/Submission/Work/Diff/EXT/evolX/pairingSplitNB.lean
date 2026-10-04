import Mathlib
import Submission.Work.Diff.EXT.mvfderiv_metric_pairing_split

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Diff.EXT.evolX

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Metric-compatibility product rule, pointwise, WITHOUT a boundaryless assumption.**

This is the version of `Work.Diff.EXT.mvfderiv_metric_pairing_split` with the hypothesis
`[I.Boundaryless]` removed (the chart-boundary case of the sphere-theorem flow needs it: the
model with corners there may have boundary).  For the Levi-Civita connection `lcOf g` of a smooth
metric `g` on `M`, and sections `W`, `Z` that are only assumed differentiable *at the point* `y`,
the directional derivative of the pairing `q ↦ g.inner q (W q) (Z q)` at `y` in an arbitrary
direction `v ∈ T_yM` splits as `⟨∇_v W, Z⟩ + ⟨W, ∇_v Z⟩`.

The proof is Mathlib's `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` for
`leviCivitaConnection` (in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean`), transported along the
definitional identifications `lcOf g = leviCivitaConnection I M` and `inner ℝ = g.inner` that hold
once `RiemannianBundle := ⟨g.toRiemannianMetric⟩` is installed.  Neither that proof nor its
ingredients mention `I.Boundaryless`; `hLC` is not needed either, since metric compatibility of the
*Levi-Civita* connection is a theorem of Mathlib
(`isMetricCompatible_leviCivitaConnection`). -/
theorem pairingSplitNB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {W Z : Π q : M, TangentSpace I q} {y : M} {v : TangentSpace I y}
    (hW : MDifferentiableAt I I.tangent
      (fun q : M => Bundle.TotalSpace.mk' E q (W q)) y)
    (hZ : MDifferentiableAt I I.tangent
      (fun q : M => Bundle.TotalSpace.mk' E q (Z q)) y) :
    mvfderiv I (fun q : M => g.inner q (W q) (Z q)) y v
      = g.inner y ((Submission.Diff.lcOf g) W y v) (Z y)
        + g.inner y (W y) ((Submission.Diff.lcOf g) Z y v) := by
  classical
  -- Endow `M` with the metric `g`: then `lcOf g` is `leviCivitaConnection I M` and `⟪·,·⟫` is
  -- `g.inner`, both definitionally.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- Metric compatibility of the Levi-Civita connection.
  have hmet := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  -- The Leibniz identity, with the direction realised by `FiberBundle.extend E v`.
  have hmain := hmet.mvfderiv_inner_eq (x := y) (FiberBundle.extend E v) hW hZ
  simp only [FiberBundle.extend_apply_self] at hmain
  -- Change the goal to the instance inner product / `leviCivitaConnection` form.
  change mvfderiv I (fun q : M => inner ℝ (W q) (Z q)) y v
      = inner ℝ ((CovariantDerivative.leviCivitaConnection I M) W y v) (Z y)
        + inner ℝ (W y) ((CovariantDerivative.leviCivitaConnection I M) Z y v)
  exact hmain

end Work.Diff.EXT.evolX
