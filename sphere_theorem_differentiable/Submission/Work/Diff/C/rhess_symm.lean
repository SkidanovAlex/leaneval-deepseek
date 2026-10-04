import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.mvfderiv_second_along_fields_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Metric compatibility at a point, from the challenge's form of it.**

The hypothesis `LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov` states the identity
`v·⟨σ, τ⟩ = ⟨∇_v σ, τ⟩ + ⟨σ, ∇_v τ⟩` only for *globally* `C^∞` sections `σ`, `τ` (and an arbitrary
direction vector `v`).  Mathlib's `CovariantDerivative.IsMetricCompatible` (the `derivMetricTensor`
form) is equivalent to the same identity for sections that are only differentiable *at the point*
`x`, and this is what the computation of the Hessian needs (its first slot is the gradient
`y ↦ ∇f(y)` of a function that is only smooth at `x`).  The bridge is the usual tensoriality of
`derivMetricTensor`: its value at `x` only depends on the *values* `σ x`, `τ x`, `v` of its
arguments, so one may replace `σ`, `τ` by globally `C^∞` sections with the same values at `x`
(`Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq`). -/
theorem mvfderiv_inner_eq_of_isMetricCompatible
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {σ τ : Π y : M, TangentSpace I y} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => inner ℝ (σ y) (τ y)) x v =
      inner ℝ (cov σ x v) (τ x) + inner ℝ (σ x) (cov τ x v) := by
  obtain ⟨Y, hYsm, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) (σ x)
  obtain ⟨Z, hZsm, hZx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) (τ x)
  have hYmd : MDiffAt (T% Y) x := hYsm.mdifferentiableAt (by simp)
  have hZmd : MDiffAt (T% Z) x := hZsm.mdifferentiableAt (by simp)
  have keyY := CovariantDerivative.derivMetricTensor_apply (cov := cov) (x := x) (σ := Y)
    (τ := Z) (X := fun _ : M => v) hYmd hZmd
  beta_reduce at keyY
  have hhm := hmet Y Z hYsm hZsm x v
  have key : cov.derivMetricTensor x (σ x) (τ x) v = 0 := by
    rw [← hYx, ← hZx, keyY, hhm]
    ring
  have h2 := CovariantDerivative.derivMetricTensor_apply (cov := cov) (x := x) (σ := σ)
    (τ := τ) (X := fun _ : M => v) hσ hτ
  beta_reduce at h2
  rw [key] at h2
  linarith

theorem rhess_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {f : M → ℝ} {x : M} (hf : CMDiffAt ∞ f x) (V W : TangentSpace I x) :
    Work.Diff.C.rhess cov f x V W = Work.Diff.C.rhess cov f x W V := by
  -- The gradient field, differentiable at `x`
  have hσmd : MDiffAt (T% (fun y : M => rgrad (I := I) f y)) x :=
    (grad_smoothAt (I := I) (F := f) (x := x) hf).mdifferentiableAt (by simp)
  -- Globally smooth extensions of `V` and `W`
  obtain ⟨X, hXsm, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) V
  obtain ⟨Y, hYsm, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := x) W
  have hXmd : MDiffAt (T% X) x := hXsm.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% Y) x := hYsm.mdifferentiableAt (by simp)
  -- `⟪∇f, ·⟫ = d% f(·)`, pointwise
  have hfun1 : (fun y : M => inner ℝ (rgrad (I := I) f y) (Y y))
      = (fun y : M => mvfderiv I f y (Y y)) := by
    funext y; exact inner_rgrad_mvfderiv f y (Y y)
  have hfun2 : (fun y : M => inner ℝ (rgrad (I := I) f y) (X y))
      = (fun y : M => mvfderiv I f y (X y)) := by
    funext y; exact inner_rgrad_mvfderiv f y (X y)
  -- metric compatibility, in the two pairings we need
  have hA := mvfderiv_inner_eq_of_isMetricCompatible cov hmet hσmd hYmd V
  rw [hfun1, ← hXx] at hA
  have hC := mvfderiv_inner_eq_of_isMetricCompatible cov hmet hσmd hXmd W
  rw [hfun2, ← hYx] at hC
  -- second derivatives of `f` commute up to the Lie bracket
  have hcl : mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)
      = mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (mlieBracket I X Y x) :=
    mvfderiv_second_along_fields_contMDiffAt hf hXsm hYsm
  rw [← inner_rgrad_mvfderiv f x (mlieBracket I X Y x)] at hcl
  -- torsion-freeness: `∇_X Y - ∇_Y X = [X,Y]`
  have htorx : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (𝕜 := ℝ) (E := E) (I := I) (M := M) cov).mp
      htor hXmd hYmd
  -- the vector of the inner product with `∇f` vanishes, by torsion-freeness
  have hpe : inner ℝ (rgrad (I := I) f x)
      (cov X x (Y x) + mlieBracket I X Y x - cov Y x (X x)) = 0 := by
    have h0 : cov X x (Y x) + mlieBracket I X Y x - cov Y x (X x) = 0 := by
      rw [← htorx]; abel
    rw [h0, inner_zero_right]
  rw [inner_sub_right, inner_add_right] at hpe
  -- conclude
  show inner ℝ (cov (fun y : M => rgrad (I := I) f y) x V) W
    = inner ℝ (cov (fun y : M => rgrad (I := I) f y) x W) V
  rw [← hXx, ← hYx]
  linarith

end Work.Diff.C
