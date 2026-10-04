import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate-frame chart matrix of a positive definite section is invertible

The section `h : Bil I M` of the question is only assumed to satisfy the lower bound
`lam · g₀.inner x v v ≤ h x v v` with `lam > 0` (no symmetry, no smoothness).  Such an `h` is
pointwise positive definite as a quadratic form, and the determinant of the matrix of *any*
positive definite bilinear form in *any* basis is non-zero: a bilinear form whose associated
quadratic form is strictly positive on non-zero vectors is separating on the left, and a matrix is
left-separating exactly when its determinant does not vanish
(`Matrix.separatingLeft_iff_det_ne_zero`).

Concretely, for the chart matrix

`Gf D h j z i k = h (D.pt j z) (cFrame (D.x₀ j) i (D.pt j z)) (cFrame (D.x₀ j) k (D.pt j z))`

of `h` in the coordinate frame of the chart at `D.x₀ j`, the frame is the image of the canonical
basis `bB` under the linear equivalence `symmL` of the tangent-bundle trivialization at the chart
centre, so the matrix is the matrix of the bilinear form `u, v ↦ h p u v` in a basis and the
linear-algebra lemma applies verbatim.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

noncomputable section

/-- **Positive definiteness implies non-singularity of the matrix in any basis** (no symmetry
hypothesis).  If the associated quadratic form `v ↦ B v v` is strictly positive on non-zero
vectors, then `B` is separating on the left, and the matrix of a left-separating form in any basis
has non-zero determinant. -/
lemma bilinForm_det_toMatrix_ne_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hpos : ∀ v : W, v ≠ 0 → 0 < B v v) :
    ((LinearMap.BilinForm.toMatrix b) B).det ≠ 0 := by
  rw [← Matrix.separatingLeft_iff_det_ne_zero]
  rw [LinearMap.BilinForm.separatingLeft_toMatrix_iff b]
  intro x hx
  by_contra hx0
  have h := hpos x hx0
  rw [hx x] at h
  exact absurd h (lt_irrefl 0)

/-- **The coordinate-frame chart matrix of a pointwise positive definite section is non-singular.**
No symmetry of `h` is assumed. -/
lemma chartMatOf_det_ne_zero_of_posDef
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).det ≠ 0 := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hp_src : p ∈ (extChartAt I x₀).source := by
    rw [hpdef]
    exact (extChartAt I x₀).map_target hy
  have hbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    simpa using hp_src
  -- the coordinate frame of the chart, as a basis
  let ee : E ≃ₗ[ℝ] TangentSpace I p :=
    (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ p hbase).symm).toLinearEquiv
  let bs : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    (Work.Diff.EXT.bB (E := E)).map ee
  have hbsLE : ∀ v : E, ee v =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ p v := by
    intro v
    exact congrFun (Bundle.Trivialization.symm_continuousLinearEquivAt_eq
      (trivializationAt E (TangentSpace I) x₀) (b := p) hbase) v
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
  have hdet : ((LinearMap.BilinForm.toMatrix bs) B).det ≠ 0 :=
    bilinForm_det_toMatrix_ne_zero bs B (fun v hv => by rw [hBapp]; exact hpos p v hv)
  -- the chart matrix is that matrix
  have hmat : (LinearMap.BilinForm.toMatrix bs) B =
      Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, Work.Diff.STE.D.chartMatOf_apply,
      ← hpdef]
    simp only [hbs, hBapp]
  rw [← hmat]
  exact hdet

end

theorem transport_det_Gf_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j) :
    (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z)).det ≠ 0 := by
  -- the lower bound makes `h` pointwise positive definite
  have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v := by
    intro x v hv
    exact lt_of_lt_of_le (mul_pos hlam (g₀.pos x v hv)) (hell x v)
  have htarget : yf (I := I) (M := M) D j z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  exact chartMatOf_det_ne_zero_of_posDef (I := I) (M := M) h (D.x₀ j) hpos htarget

end Work.Diff.STE.B3
