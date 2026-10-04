import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false

/-- **The curvature of a smooth connection as a smooth section.**
If `cov` is a `C^∞` covariant derivative and `X, Y, Z` are smooth vector fields, then
`y ↦ R(X,Y)Z(y) = curv cov X Y Z y` is a smooth vector field.

This is the "second derivative" regularity step: `curv cov X Y Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z`
is a difference of three terms, each of which is a `C^∞` section by
`contMDiff_cov_apply` (applied twice for the first two terms) and the smoothness of the Lie bracket
`ContMDiffAt.mlieBracket_vectorField` (for the third). -/
theorem contMDiff_curv_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (T% (fun y : M => curv cov X Y Z y)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  -- the Lie bracket of two smooth fields is smooth
  have hbr : CMDiff ∞ (T% (mlieBracket I X Y)) := by
    intro y
    exact (hX y).mlieBracket_vectorField (hY y) (by simp)
  -- the three terms of `curv`
  have h1 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hY) hX
  have h2 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (X y')) y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hX) hY
  have h3 : CMDiff ∞ (T% (fun y : M => cov Z y (mlieBracket I X Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hZ hbr
  change CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y)
      - cov (fun y' : M => cov Z y' (X y')) y (Y y) - cov Z y (mlieBracket I X Y y)))
  exact (h1.sub_section h2).sub_section h3

/-- `rmP (g) y (A y) (B y) (C y) (D y)` is a smooth function of `y` when `A,B,C,D` are smooth
sections of the tangent bundle and `g` is a smooth metric (for the Levi-Civita connection of `g`).

Suggested route: `rmP g y (A y) (B y) (C y) (D y) = g.inner y (rmVec (lcOf g) y (A y) (B y) (D y))`
(`rfl`), then rewrite `rmVec` as `curvVec` (`Work.Diff.GE.rmVec_eq_curvVec`, `Work.Diff.GE.rmP_eq`)
and `curvVec … (A y)(B y)(D y) = curv (lcOf g) A B D y` for the *given* smooth fields
(`Submission.CurvatureVec.curvVec_eq`).  Smoothness of `y ↦ curv (lcOf g) A B D y` then follows from
the definition `curv cov X Y Z = fun x => cov (fun y => cov Z y (Y y)) x (X x) - …`
(`commons` `Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply`, applied
twice per term, and `ContMDiff.mlieBracket_vectorField` / `ContMDiffAt.mlieBracket_vectorField` for
the bracket, plus `ContMDiff.sub_section`), and finally `ContMDiff.inner_bundle` pairs the two smooth
sections.  Note `hLC g` gives `Nonempty (ContMDiffCovariantDerivative (lcOf g) ∞)`. -/
theorem contMDiff_rmP_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) := by
  -- the connection of `g` is the smooth Levi-Civita connection and `g.inner` is the instance inner
  -- product of `⟨g.toRiemannianMetric⟩`
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  -- `y ↦ R(A,B)D(y)` is a smooth section
  have hcurv : CMDiff ∞ (T% (fun y : M => curv (lcOf g) A B D y)) :=
    contMDiff_curv_fields (lcOf g) hcov hA hB hD
  -- rewrite `rmP` as the pairing of two smooth sections
  have hfun : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => inner ℝ (curv (lcOf g) A B D y) (C y) := by
    funext y
    show (g.inner y (rmVec (lcOf g) y (A y) (B y) (D y))) (C y) = _
    rw [rmVec_eq_curvVec (lcOf g) hcov y (A y) (B y) (D y),
      Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl]
    rfl
  rw [hfun]
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => curv (lcOf g) A B D y)
    (w := C) hcurv hC

end Work.Diff.GE
