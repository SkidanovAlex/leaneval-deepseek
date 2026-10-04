import Mathlib
import Submission.Work.Diff.GE.frame_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false in
/-- An `IsONFrame g x e` (the frozen orthonormality condition
`g.inner x (e i) (e j) = if i = j then 1 else 0`) is linearly independent: orthogonality for the
positive definite form `g.inner x` forces independence.  (Install
`letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩`, under which
`inner ℝ` is definitionally `g.inner`, and use `orthonormal_iff_ite` together with
`Orthonormal.linearIndependent`.) -/
theorem linearIndependent_of_isONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) : LinearIndependent ℝ e := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have h : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
    exact he i j
  exact h.linearIndependent

end Work.Diff.GE
