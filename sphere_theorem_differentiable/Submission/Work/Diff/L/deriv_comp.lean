import Mathlib
import Submission.Work.Diff.L.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

/-- The chain rule along a curve, in `HasDerivAt` form: the derivative of `s ↦ u (γ s)` is
`mvfderiv I u (γ t)` applied to the velocity `curveVelocity I γ t`.
(The existing `Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve` gives the `deriv` form.) -/
theorem deriv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    {u : M → ℝ} (hu : CMDiff ∞ u) {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) {t : ℝ} (ht : t ∈ V) :
    HasDerivAt (fun s => u (γ s)) (mvfderiv I u (γ t) (curveVelocity (I := I) γ t)) t := by
  -- `γ` is smooth at `t` (the set `V` is open) and `u` is smooth everywhere, so both are
  -- differentiable at the relevant points ...
  have hγat : ContMDiffAt 𝓘(ℝ) I ∞ γ t := hγ.contMDiffAt (hV.mem_nhds ht)
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t := hγat.mdifferentiableAt (by simp)
  have humid : MDifferentiableAt I 𝓘(ℝ) u (γ t) := hu.mdifferentiableAt (by simp)
  -- ... whence `u ∘ γ` is differentiable as a function `ℝ → ℝ`, with `HasFDerivAt` given by the
  -- manifold chain rule.
  have hcomp := humid.hasMFDerivAt.comp t hγmd.hasMFDerivAt
  -- The `deriv` form of the chain rule identifies the value of that derivative.
  have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (g := u) (γ := γ) humid hγmd
  rw [show mvfderiv I u (γ t) (curveVelocity (I := I) γ t) = deriv (u ∘ γ) t from hkey]
  exact hcomp.hasFDerivAt.differentiableAt.hasDerivAt

end Work.Diff.L
