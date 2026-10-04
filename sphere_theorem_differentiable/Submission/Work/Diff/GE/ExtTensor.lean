import Mathlib
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Curvature

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Ext` pattern for the second covariant derivative of a field-level tensor

`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` and `cov2RmExt g x u V A B C D` are defined as
`mvfderiv` of a component function minus the Leibniz corrections.  This is an instance of a general
pattern: for a *field-level tensor* `τ` of arity `ι` (a function of `ι` smooth fields with values in
functions on `M`), the first and second covariant derivatives are

`extD cov τ x X F = mvfderiv (τ F) x (X x) - ∑ i, τ (F with slot i replaced by ∇_X F_i) x`,

`extDD cov τ x X Y F = mvfderiv (fun y ↦ extD cov τ y Y F) x (X x) - extD cov τ x (∇_X Y) F
   - ∑ i, extD cov τ x Y (F with slot i replaced by ∇_X F_i)`.

The main theorem about this pattern, the *Ricci identity* for `τ`, is that the antisymmetrised
second derivative is the algebraic curvature contraction
`-∑ i, τ (F with slot i replaced by R(X,Y) F_i)`; see `Work.Diff.GE.extDD_antisymm`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Notation-free wrapper: the section `X` is `C^∞`. -/
abbrev SmoothFieldT (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)

/-- Notation-free wrapper: the function `f : M → ℝ` is `C^∞`. -/
abbrev SmoothFunT (f : M → ℝ) : Prop := CMDiff ∞ f

/-- Notation-free wrapper: `cov` is a smooth covariant derivative. -/
abbrev CovSmooth (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ContMDiffCovariantDerivative cov ∞

/-- A tuple of smooth sections. -/
abbrev SmoothTuple {ι : Type*} (F : ι → (Π y : M, TangentSpace I y)) : Prop :=
  ∀ i, SmoothFieldT (I := I) (M := M) (F i)

/-- `∇_X G`, the covariant derivative of the field `G` in the direction of the field `X`. -/
abbrev covAlong (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X G : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y := fun y => cov G y (X y)

/-- A field-level tensor of arity `ι`. -/
abbrev ExtTensor (ι : Type*) : Type _ := (ι → (Π y : M, TangentSpace I y)) → (M → ℝ)

/-- `F` with slot `i` replaced by `∇_X F_i`. -/
abbrev upd (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [DecidableEq ι] (X : Π y : M, TangentSpace I y)
    (F : ι → (Π y : M, TangentSpace I y)) (i : ι) : ι → (Π y : M, TangentSpace I y) :=
  Function.update F i (covAlong cov X (F i))

/-- The first `Ext` derivative of a field-level tensor `τ` of arity `ι`. -/
noncomputable def extD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ExtTensor (I := I) (M := M) ι)
    (x : M) (X : Π y : M, TangentSpace I y) (F : ι → (Π y : M, TangentSpace I y)) : ℝ :=
  mvfderiv I (τ F) x (X x) - ∑ i, τ (upd cov X F i) x

/-- The second `Ext` derivative of a field-level tensor `τ` of arity `ι`. -/
noncomputable def extDD (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ExtTensor (I := I) (M := M) ι)
    (x : M) (X Y : Π y : M, TangentSpace I y) (F : ι → (Π y : M, TangentSpace I y)) : ℝ :=
  mvfderiv I (fun y : M => extD cov τ y Y F) x (X x)
    - extD cov τ x (covAlong cov X Y) F
    - ∑ i, extD cov τ x Y (upd cov X F i)

/-- `extD` written out. -/
theorem extD_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ExtTensor (I := I) (M := M) ι)
    (x : M) (X : Π y : M, TangentSpace I y) (F : ι → (Π y : M, TangentSpace I y)) :
    extD cov τ x X F = mvfderiv I (τ F) x (X x) - ∑ i, τ (upd cov X F i) x :=
  rfl

/-- `extDD` written out. -/
theorem extDD_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ExtTensor (I := I) (M := M) ι)
    (x : M) (X Y : Π y : M, TangentSpace I y) (F : ι → (Π y : M, TangentSpace I y)) :
    extDD cov τ x X Y F
      = mvfderiv I (fun y : M => extD cov τ y Y F) x (X x)
        - extD cov τ x (covAlong cov X Y) F
        - ∑ i, extD cov τ x Y (upd cov X F i) :=
  rfl

/-- `covAlong` of a smooth field in a smooth direction is smooth. -/
theorem cmdiff_covAlong (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovSmooth cov)
    {X G : Π y : M, TangentSpace I y} (hX : SmoothFieldT (I := I) (M := M) X)
    (hG : SmoothFieldT (I := I) (M := M) G) :
    SmoothFieldT (I := I) (M := M) (covAlong cov X G) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hG hX

/-- The curvature as a combination of `covAlong`s. -/
theorem curv_eq_covAlong (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π y : M, TangentSpace I y) :
    curv cov X Y Z
      = covAlong cov X (covAlong cov Y Z) - covAlong cov Y (covAlong cov X Z)
        - covAlong cov (mlieBracket I X Y) Z :=
  rfl

/-- Updating one slot of a smooth tuple preserves smoothness. -/
theorem smoothTuple_upd (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovSmooth cov) {ι : Type*} [DecidableEq ι] {X : Π y : M, TangentSpace I y}
    (hX : SmoothFieldT (I := I) (M := M) X)
    {F : ι → (Π y : M, TangentSpace I y)} (hF : SmoothTuple (I := I) (M := M) F) (i : ι) :
    SmoothTuple (I := I) (M := M) (upd cov X F i) := by
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [upd, Function.update_self]
    exact cmdiff_covAlong cov hcov hX (hF j)
  · rw [upd, Function.update_of_ne hj]
    exact hF j

/-- **Expansion of `extDD`**: the second `Ext` derivative written as an explicit combination of
`mvfderiv`s of `τ` and of the connection corrections.  This is `extDD` with the first `Ext`
derivative unfolded and the derivative of the resulting difference/sum split. -/
theorem extDD_expand (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovSmooth cov)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      SmoothTuple (I := I) (M := M) F → SmoothFunT (I := I) (M := M) (τ F))
    (x : M) (X Y : Π y : M, TangentSpace I y) (hY : SmoothFieldT (I := I) (M := M) Y)
    (F : ι → (Π y : M, TangentSpace I y)) (hF : SmoothTuple (I := I) (M := M) F) :
    extDD cov τ x X Y F
      = mvfderiv I (fun y : M => mvfderiv I (τ F) y (Y y)) x (X x)
        - ∑ i, mvfderiv I (fun y : M => τ (upd cov Y F i) y) x (X x)
        - mvfderiv I (τ F) x ((covAlong cov X Y) x)
        + ∑ i, τ (upd cov (covAlong cov X Y) F i) x
        - ∑ i, mvfderiv I (τ (upd cov X F i)) x (Y x)
        + ∑ i, ∑ k, τ (upd cov Y (upd cov X F i) k) x := by
  have hG : ∀ i, SmoothTuple (I := I) (M := M) (upd cov Y F i) :=
    fun i => smoothTuple_upd cov hcov hY hF i
  have hfun : (fun y : M => extD cov τ y Y F)
      = (fun y : M => mvfderiv I (τ F) y (Y y))
        - (fun y : M => ∑ i, τ (upd cov Y F i) y) := by
    funext y
    rw [Pi.sub_apply, extD_eq]
  have hmd1 : MDiffAt (fun y : M => mvfderiv I (τ F) y (Y y)) x :=
    ((Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (hτ F hF) hY).mdifferentiableAt
      (by simp))
  have hmd2 : MDiffAt (fun y : M => ∑ i, τ (upd cov Y F i) y) x :=
    ((ContMDiff.sum (fun i _ => hτ _ (hG i))).mdifferentiableAt (by simp))
  rw [extDD_eq, hfun, mvfderiv_sub hmd1 hmd2]
  simp only [sub_apply]
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ)
    (fun i => fun y : M => τ (upd cov Y F i) y) (fun i => hτ _ (hG i)) x (X x)]
  simp only [extD_eq, Finset.sum_sub_distrib]
  ring

/-- **Diagonal extraction for a double sum.**  If `B i k = A k i` off the diagonal then the
double sum of the differences is the sum of the diagonal differences. -/
theorem sum_univ_univ_sub_eq_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : ι → ι → ℝ)
    (h : ∀ i k, k ≠ i → A k i = B i k) :
    (∑ i, ∑ k, (A i k - B i k)) = ∑ i, (A i i - B i i) := by
  have hsplit : ∀ i : ι, (∑ k, (A i k - B i k))
      = (∑ k, (A i k - A k i)) + (∑ k, (A k i - B i k)) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hzero : (∑ i, ∑ k, (A i k - A k i)) = 0 := by
    have h1 : (∑ i, ∑ k, (A i k - A k i)) = (∑ i, ∑ k, A i k) - (∑ i, ∑ k, A k i) := by
      simp only [Finset.sum_sub_distrib]
    have h2 : (∑ i, ∑ k, A k i) = (∑ i, ∑ k, A i k) := by
      rw [Finset.sum_comm]
    rw [h1, h2, sub_self]
  have hdiag : ∀ i : ι, (∑ k, (A k i - B i k)) = A i i - B i i := by
    intro i
    refine Finset.sum_eq_single i ?_ ?_
    · intro k _ hk
      rw [h i k hk, sub_self]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hzero, zero_add]
  exact Finset.sum_congr rfl fun i _ => hdiag i

end Work.Diff.GE
