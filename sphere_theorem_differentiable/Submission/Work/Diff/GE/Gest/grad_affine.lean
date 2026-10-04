import Mathlib
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem grad_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {u : M → ℝ} (hu : CMDiff ∞ u) (a b : ℝ) (x : M) :
    gradSq g (fun y => a * u y + b) x = a ^ 2 * gradSq g u x := by
  -- `gradSq g u x = ∑ i, (mvfderiv I u x (onFrame g x i))^2`, so it suffices to show the
  -- directional derivative of `y ↦ a * u y + b` is `a` times that of `u` in every frame direction.
  have hu' : MDifferentiableAt I 𝓘(ℝ, ℝ) u x := hu.mdifferentiableAt (by simp)
  have hd : ∀ v : TangentSpace I x,
      mvfderiv I (fun y => a * u y + b) x v = a * mvfderiv I u x v := by
    intro v
    have h1 : (fun y : M => a * u y + b) = (fun _ : M => a) • u + (fun _ : M => b) := by
      funext z; simp [smul_eq_mul]
    rw [h1, mvfderiv_add ((mdifferentiableAt_const (c := a)).smul hu')
          (mdifferentiableAt_const (c := b)),
        mvfderiv_smul (mdifferentiableAt_const (c := a)) hu']
    simp [mvfderiv_const, smul_eq_mul]
  simp only [gradSq]
  have key : ∀ i : Fin (Module.finrank ℝ E),
      (mvfderiv I (fun y : M => a * u y + b) x (onFrame g x i)) ^ 2
        = a ^ 2 * (mvfderiv I u x (onFrame g x i)) ^ 2 := by
    intro i; rw [hd (onFrame g x i)]; ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum]

end Work.Diff.GE.Gest
