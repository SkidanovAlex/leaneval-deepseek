import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.D.GalODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.psi

/-!
# The chart matrix of a positive definite symmetric section has positive determinant

This file proves `Work.Diff.STE.D.psi.chartMatOf_pd_det_pos`: on the target of the chart at `x₀`,
the determinant of the chart matrix of the perturbed section `g₀ + genMap D ε c` is positive,
whenever that section is pointwise positive definite (the hypothesis `IsPos`, which is the first
branch of `Work.Diff.STE.D.psi`) and symmetric.

The mathematical content is the standard fact that a symmetric positive definite bilinear form has
a positive determinant in any basis, applied to the coordinate frame
`eᵢ = frameVector I x₀ p (bB i)` of the chart at `x₀` (`p = (extChartAt I x₀).symm y`).
The frame is a basis because it is the image of the basis `bB = Module.finBasis ℝ E` under the
linear equivalence `TangentSpace I p ≃ₗ[ℝ] E` inverse to the tangent-bundle trivialisation at
`x₀`.  The chart matrix is exactly the matrix of the bilinear form `h p` in this basis, so
`Matrix.PosDef.det_pos` applies.
-/

/-- **A positive definite symmetric section has positive determinant in the coordinate frame of a
chart.**  If `h` is symmetric and pointwise positive definite at every point of `M` covered by the
chart at `x₀`, then the determinant of its chart matrix `Work.Diff.STE.D.chartMatOf h x₀ y` is
positive at every chart coordinate `y ∈ (extChartAt I x₀).target`. -/
lemma chartMatOf_det_pos_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    0 < (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).det := by
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
  exact Matrix.PosDef.det_pos hpd

theorem chartMatOf_pd_det_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    0 < (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M)
      (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y)).det :=
  chartMatOf_det_pos_of_posDef (I := I) (M := M)
    (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) x₀
    (Work.Diff.STE.D.isSymm_addSec (I := I) (M := M) (ι₀ := ι₀)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)
      (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c))
    (fun x v hv => hc x v hv) hy

end Work.Diff.STE.D.psi
