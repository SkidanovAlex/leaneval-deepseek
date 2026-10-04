import Mathlib
import Submission.Work.Diff.GE.kato_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Metric compatibility of the Levi-Civita connection of `g`, instance-free form.**

For the Levi-Civita connection `lcOf g` of a smooth metric `g` and globally smooth fields `Y`, `Z`,
the directional derivative of the pairing `y ↦ g.inner y (Y y) (Z y)` at `x` in direction `v`
splits as `g(∇_v Y, Z) + g(Y, ∇_v Z)`.

This is Mathlib's `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` for
`leviCivitaConnection`.  The transport is definitional: with the instance
`RiemannianBundle := ⟨g.toRiemannianMetric⟩` installed, `lcOf g` *is*
`CovariantDerivative.leviCivitaConnection I M` and the instance inner product `⟪·,·⟫` *is* `g.inner`
(see `Work.Diff.GE.inner_eq_metric`), so a `change` puts the goal in the form in which Mathlib's
lemma applies verbatim.  The direction is realised by the extension
`FiberBundle.extend E v`, whose value at `x` is `v`. -/
theorem kato_mvfderiv_inner_lc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) (v : TangentSpace I x) {Y Z : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x v =
      g.inner x (lcOf g Y x v) (Z x) + g.inner x (Y x) (lcOf g Z x v) := by
  classical
  -- Endow `M` with the metric `g`: then `lcOf g` is `leviCivitaConnection I M` and `⟪·,·⟫` is
  -- `g.inner`, both definitionally.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- Metric compatibility of the Levi-Civita connection.
  have hmet := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  -- Globally smooth fields are differentiable at every point.
  have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  -- The Leibniz identity, with the direction realised by `FiberBundle.extend E v`.
  have hmain := hmet.mvfderiv_inner_eq (x := x) (FiberBundle.extend E v) hY' hZ'
  simp only [FiberBundle.extend_apply_self] at hmain
  -- Change the goal to the instance inner product / `leviCivitaConnection` form.
  change mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v
      = inner ℝ ((CovariantDerivative.leviCivitaConnection I M) Y x v) (Z x)
        + inner ℝ (Y x) ((CovariantDerivative.leviCivitaConnection I M) Z x v)
  exact hmain

end Work.Diff.GE
