import Mathlib
import Submission.Work.Diff.GE.Gest.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Laplacian is affine on affine functions

`Δ_g (a·u + b) = a·Δ_g u` for `u : M → ℝ` smooth and `a b : ℝ`.

This is the "constants have zero Laplacian + linearity in the scalar multiple" part of the affine
calculus of `laplAt` used in the maximum principle for the gradient estimate.

`laplAt g U x = ∑ i, hessAt g U x (e i) (e i)` in the `g`-orthonormal frame `onFrame g x`, and
`hessAt` is built from two first derivatives along the chosen smooth extension of a tangent
vector.  So the proof has two ingredients:

* the pointwise linearity `d% (fun y ↦ a * u y + b) y = a • d% u y` of the `mvfderiv` (Mathlib's
  `mvfderiv_smul` / `mvfderiv_add` / `mvfderiv_const`), and
* the fact that `y ↦ d% u y (W y)` is again smooth for a smooth field `W`
  (`mvfderiv_apply_contMDiff`, which supplies the differentiability needed to pull the constant
  `a` out of the outer `mvfderiv`).
-/

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- `mvfderiv` of a constant multiple: `d(c·u) = c · du`, pointwise in the direction `v`. -/
lemma mvfderiv_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {u : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) (c : ℝ) (v : TangentSpace I x) :
    mvfderiv I (fun y => c * u y) x v = c * mvfderiv I u x v := by
  have h1 : (fun y : M => c * u y) = (fun _ : M => c) • u := by
    funext y; simp [smul_eq_mul]
  rw [h1, mvfderiv_smul (mdifferentiableAt_const (c := c)) hu, mvfderiv_const c,
    ContinuousLinearMap.zero_smulRight, add_zero]
  simp [smul_eq_mul]

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem lapl_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {u : M → ℝ} (hu : CMDiff ∞ u) (a b : ℝ) (x : M) :
    laplAt g (fun y => a * u y + b) x = a * laplAt g u x := by
  -- `u` is differentiable everywhere.
  have hu' : ∀ y : M, MDifferentiableAt I 𝓘(ℝ, ℝ) u y :=
    fun y => hu.mdifferentiableAt (by simp)
  -- Pointwise linearity of the first derivative of the affine function.
  have hd : ∀ y : M, mvfderiv I (fun z : M => a * u z + b) y = a • mvfderiv I u y := by
    intro y
    have h1 : (fun z : M => a * u z + b) = (fun _ : M => a) • u + (fun _ : M => b) := by
      funext z; simp [smul_eq_mul]
    rw [h1, mvfderiv_add ((mdifferentiableAt_const (c := a)).smul (hu' y))
          (mdifferentiableAt_const (c := b)),
        mvfderiv_smul (mdifferentiableAt_const (c := a)) (hu' y)]
    simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero]
  -- Pointwise linearity of the Hessian in the frame directions.
  have hhess : ∀ w : TangentSpace I x,
      hessAt g (fun y => a * u y + b) x w w = a * hessAt g u x w w := by
    intro w
    have hW : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_contMDiff x w
    -- the first directional derivative of `u` along the smooth field `smoothExt x w` is smooth
    have hGs : CMDiff ∞ (fun y : M => mvfderiv I u y (smoothExt x w y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hu hW
    have hkey : mvfderiv I (fun y : M => mvfderiv I (fun z : M => a * u z + b) y
          (smoothExt x w y)) x w
        = a * mvfderiv I (fun y : M => mvfderiv I u y (smoothExt x w y)) x w := by
      have heq : (fun y : M => mvfderiv I (fun z : M => a * u z + b) y (smoothExt x w y))
          = (fun y : M => a * mvfderiv I u y (smoothExt x w y)) := by
        funext y; rw [hd y]; rfl
      rw [heq]
      exact mvfderiv_const_mul (hGs.mdifferentiableAt (by simp)) a w
    simp only [hessAt]
    rw [hkey, hd x]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- Assemble the frame sum.
  simp only [laplAt]
  rw [Finset.sum_congr rfl (fun i _ => hhess (onFrame g x i)), Finset.mul_sum]

end Work.Diff.GE.Gest
