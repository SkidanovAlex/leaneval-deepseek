import Mathlib
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# The chart matrix of a positive definite symmetric section is positive definite

This file proves `Work.Diff.STE.B3.chartMatOf_posDef`: on the target of the chart at `x₀`, the
chart matrix of a bilinear section `h` which is symmetric and pointwise positive definite is a
positive definite matrix (`Matrix.PosDef`).

The content is the standard fact that a symmetric positive definite bilinear form has a positive
definite matrix in any basis, applied to the coordinate frame `eᵢ = frameVector I x₀ p (bB i)` of
the chart at `x₀` (with `p = (extChartAt I x₀).symm y`).  The frame is a basis because it is the
image of the basis `bB = Module.finBasis ℝ E` under the linear equivalence
`TangentSpace I p ≃ₗ[ℝ] E` inverse to the tangent-bundle trivialisation at `x₀`, and the chart
matrix is exactly the matrix of the bilinear form `h p` in this basis, so
`LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix` applies.

This is the `Matrix.PosDef` strengthening of `Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef`
(which only concludes positivity of the determinant).
-/

/-- **A symmetric positive definite section has a positive definite chart matrix in the coordinate
frame of a chart.**  If `h` is symmetric and pointwise positive definite at every point of `M`
covered by the chart at `x₀`, then its chart matrix `Work.Diff.STE.D.chartMatOf h x₀ y` is positive
definite at every chart coordinate `y ∈ (extChartAt I x₀).target`. -/
lemma chartMatOf_posDef_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).PosDef := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  -- the point of the chart target is in the source of the chart, hence in the base set of the
  -- tangent-bundle trivialisation at `x₀`
  have hp_src : p ∈ (extChartAt I x₀).source := by
    rw [hpdef]
    exact (extChartAt I x₀).map_target hy
  have hbase : p ∈ (FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa using hp_src
  -- the coordinate frame of the chart, as a basis
  let ee : E ≃ₗ[ℝ] TangentSpace I p :=
    (((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ p hbase).symm).toLinearEquiv
  let bs : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    (Work.Diff.EXT.bB (E := E)).map ee
  have hbsLE : ∀ v : E, ee v =
      (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ p v := by
    intro v
    exact congrFun (Bundle.Trivialization.symm_continuousLinearEquivAt_eq
      (FiberBundle.trivializationAt E (TangentSpace I) x₀) (b := p) hbase) v
  have hbs : ∀ i, bs i = Submission.Geodesic.frameVector (I := I) x₀ p
      (Work.Diff.EXT.bB (E := E) i) := by
    intro i
    rw [Module.Basis.map_apply, hbsLE]
    rfl
  -- the section as a bilinear form on the tangent space at `p`
  let B : LinearMap.BilinForm ℝ (TangentSpace I p) :=
    LinearMap.mk₂ ℝ (fun u v => h p u v)
      (by intro u v w; rw [map_add, add_apply])
      (by intro c u v; rw [map_smul, smul_apply])
      (by intro u v w; exact map_add ((h p) u) v w)
      (by intro c u v; exact map_smul ((h p) u) c v)
  have hBapp : ∀ u v, B u v = h p u v := fun u v => LinearMap.mk₂_apply ℝ _ u v
  have hBsymm : B.IsSymm := ⟨fun u v => hsym p u v⟩
  have hBpos : B.toQuadraticMap.PosDef := by
    intro v hv
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact hpos p v hv
  have hpd : (LinearMap.BilinForm.toMatrix bs B).PosDef :=
    (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix bs B hBsymm).mp hBpos
  -- the chart matrix is that matrix
  have hmat : LinearMap.BilinForm.toMatrix bs B =
      Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, Work.Diff.STE.D.chartMatOf_apply,
      ← hpdef]
    simp only [hbs, hBapp]
  rw [← hmat]
  exact hpd

theorem chartMatOf_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).PosDef :=
  chartMatOf_posDef_of_posDef (I := I) (M := M) h x₀ hsym hpos hy

end Work.Diff.STE.B3
