import Mathlib
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Metric-compatibility product rule, pointwise in the sections.** For the Levi-Civita connection
`lcOf g` of a smooth metric `g` on `M`, and sections `W`, `Z` that are only assumed differentiable
*at the point* `y`, the directional derivative of the pairing `q ↦ g.inner q (W q) (Z q)` at `y` in
an arbitrary direction `v ∈ T_yM` splits as `⟨∇_v W, Z⟩ + ⟨W, ∇_v Z⟩`.

This is Mathlib's `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` for
`leviCivitaConnection`, transported along the definitional identifications
`lcOf g = leviCivitaConnection I M` and `inner ℝ = g.inner` that hold once
`RiemannianBundle := ⟨g.toRiemannianMetric⟩` is installed, exactly as in the existing
`Work.Diff.GE.kato_mvfderiv_inner_lc` -- except that the latter assumes *globally* smooth `W`, `Z`,
whereas here only differentiability at the single point `y` is required (which is what the
chart-frame computation `Work.Diff.EXT.cov_chartFrame_chartCoord` needs: its section is only
smooth on the chart).

`hLC : LCSmooth I M` supplies, for each `g`, `IsMetricCompatible (lcOf g)` as `(hLC g).2.2`.

(Stated with the plain `MDifferentiableAt I I.tangent (fun q ↦ TotalSpace.mk' E q (W q)) y`
instead of the scoped `MDiffAt (T% W) y` notation so that it elaborates without `open scoped`.) -/
theorem mvfderiv_metric_pairing_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
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
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hmain := hmet.mvfderiv_inner_eq (x := y) (FiberBundle.extend E v) hW hZ
  simp only [FiberBundle.extend_apply_self] at hmain
  change mvfderiv I (fun q : M => inner ℝ (W q) (Z q)) y v
      = inner ℝ ((CovariantDerivative.leviCivitaConnection I M) W y v) (Z y)
        + inner ℝ (W y) ((CovariantDerivative.leviCivitaConnection I M) Z y v)
  exact hmain

end Work.Diff.EXT
