import Mathlib
import Submission.Work.Diff.GE.ExtTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **The Ricci identity for the `Ext` pattern** (the antisymmetrised second covariant derivative of
a field-level tensor is the algebraic curvature contraction).

`Work.Diff.GE.extD cov τ x X F = mvfderiv (τ F) x (X x) - ∑ i, τ (upd cov X F i) x` is the first
covariant derivative of the field-level tensor `τ` in the direction `X`, and
`Work.Diff.GE.extDD cov τ x X Y F` is the second one (`Y` then `X`; see the module
`Submission.Work.Diff.GE.ExtTensor` for the definitions, and the already proved
`Work.Diff.GE.extDD_expand` for `extDD` written out with the `mvfderiv`s split).  The displayed
identity says that the antisymmetrisation in the two derivative directions `X`, `Y` is minus the
contraction of `τ` with the curvature `R(X,Y)` in each of the `ι` slots of `τ`.

Mathematical proof (all fields smooth; `∇_Z G` abbreviates `covAlong cov Z G`, the field
`fun y => cov G y (Z y)`; `F^{i,Z} := Function.update F i (∇_Z F i)`):

Using `extDD_expand` on both `extDD X Y F` and `extDD Y X F`, the `mvfderiv` terms appearing twice
(`∑ i, mvfderiv (τ (F^{i,X})) x (Y x)` and `∑ i, mvfderiv (τ (F^{i,Y})) x (X x)`) cancel, leaving

`Δ = [mvfderiv (fun y ↦ mvfderiv (τ F) y (Y y)) x (X x)
      - mvfderiv (fun y ↦ mvfderiv (τ F) y (X y)) x (Y x)]
     - [extD (∇_X Y) F - extD (∇_Y X) F] + (double sums)`.

The bracket is `mvfderiv (τ F) x (mlieBracket I X Y x)` by
`Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields` (Clairaut), and by
torsion-freeness (`Submission.Curvature.torsion_zero_bracket` applied to `htor`) this is
`mvfderiv (τ F) x ((∇_X Y) x) - mvfderiv (τ F) x ((∇_Y X) x)`; combined with `Work.Diff.GE.extD_eq`
this gives `∑ i, τ (F^{i,∇_X Y}) x - ∑ i, τ (F^{i,∇_Y X}) x`.

The double sums reduce, via `Function.update_comm` and the generic already proved fact
`Work.Diff.GE.sum_univ_univ_sub_eq_diag`, to the diagonal
`∑ i, (τ (F^{i,X}{}^{i,∇_Y}) x - τ (F^{i,Y}{}^{i,∇_X}) x)`, i.e.
`∑ i, (τ (F with slot i ← ∇_Y∇_X F_i) x - τ (F with slot i ← ∇_X∇_Y F_i) x)`.

Altogether `Δ = ∑ i ( τ (F^{i,∇_X Y}) x - τ (F^{i,∇_Y X}) x + τ (F with i ← ∇_Y∇_X F_i) x
- τ (F with i ← ∇_X∇_Y F_i) x )`, and the four fields occurring in slot `i` combine, using the
`C^∞(M)`-linearity of `τ` in that slot (`hτ_add`, `hτ_smul`), into the single field
`∇_Y∇_X F_i - ∇_X∇_Y F_i + ∇_{∇_XY}F_i - ∇_{∇_YX}F_i = - curv cov X Y (F i)`
(by `Work.Diff.GE.curv_eq_covAlong`, torsion-freeness `∇_XY - ∇_YX = mlieBracket I X Y` and
linearity of `cov (F i) y` in its direction argument), which is the stated right-hand side. -/
theorem extDD_antisymm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) (htor : cov.torsion = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ F : ι → (Π y : M, TangentSpace I y),
      Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
        Work.Diff.GE.SmoothFunT (I := I) (M := M) (τ F))
    (hτ_add : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G H : Π y : M, TangentSpace I y),
      τ (Function.update F i (G + H)) = τ (Function.update F i G) + τ (Function.update F i H))
    (hτ_smul : ∀ (F : ι → (Π y : M, TangentSpace I y)) (i : ι)
        (G : Π y : M, TangentSpace I y) (c : ℝ),
      τ (Function.update F i (c • G)) = c • τ (Function.update F i G))
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (F : ι → (Π y : M, TangentSpace I y))
    (hF : Work.Diff.GE.SmoothTuple (I := I) (M := M) F) :
    Work.Diff.GE.extDD cov τ x X Y F - Work.Diff.GE.extDD cov τ x Y X F
      = - (Finset.univ.sum
            (fun i => τ (Function.update F i
              (fun y => LeanEval.Geometry.SphereTheorem.curv cov X Y (F i) y)) x)) := by
  sorry

end Work.Diff.GE
