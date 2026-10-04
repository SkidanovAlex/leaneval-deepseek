import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.fill.bilChart_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The change of chart for the volume densities of the Layer B3 atlas

The volume density of the chart at `x₀` is the square root of the determinant of the *chart matrix*
of the metric in that chart (`B3Data.dens`), and on the overlap of two charts the two densities are
related by the absolute value of the determinant of the chart transition:

`dens i (coord i p) = |det (tangentCoordChange (x₀ i) (x₀ j) p)| * dens j (coord j p)`.

The mathematical content is the classical gauge formula for a Gram matrix.  Write `σᵢ_a` for the
trivialisation-constant frame of the chart at `x₀ i` and `σⱼ_c` for that of the chart at `x₀ j`, and
let `A` be the matrix of the change of frame (`chartCoeffMat`), i.e. the matrix of the change of
fibre coordinates `(trivializationAt … x₀ j).linearMapAt p ∘ (trivializationAt … x₀ i).symm p`.
Then `σᵢ_a = ∑ c, A a c • σⱼ_c`, so the Gram matrices satisfy

`G_i = A * G_j * Aᵀ`   (`chartMatFun_mul`, from the Layer B2 gauge formula `bilChart_change`),

whence `det G_i = det A * det G_j * det A` and, taking square roots,
`√(det G_i) = |det A| · √(det G_j)`.

The determinant `det A` is the determinant of the change of fibre coordinates of the tangent bundle,
which is `tangentCoordChange x₀i x₀j p` (`det_chartCoeffMat`, via
`VectorBundleCore.trivializationAt_coordChange_eq`).

Everything is stated for the *trivialisation* frames, so that the ingredients are the Layer B2 gauge
formula and the tangent-bundle core; the metric only enters through the bilinearity of `g.inner`.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix

namespace Work.Diff.STE.B3

set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- The flat coordinate of `p` in the chart at `x₀`, read back in the model space, is the chart
coordinate of `p`. -/
lemma flatToE_coord (x₀ p : M) :
    Work.Diff.STE.flatToE (I := I) x₀ (Work.Diff.STE.coord (I := I) x₀ p)
      = (extChartAt I x₀) p := by
  simp only [Work.Diff.STE.flatToE, Work.Diff.STE.coord]
  rw [show (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p) from by abel]
  exact LinearEquiv.symm_apply_apply _ _

/-- **The matrix of the change of trivialisation frame** from the chart at `x₀` to that at `x₁`, at
the point `p`: the coordinates of the trivialisation-constant vectors of the chart at `x₀` in the
trivialisation at `x₁`. -/
noncomputable def chartCoeffMat (x₀ x₁ p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun a c => ((Module.finBasis ℝ E).repr
    ((Trivialization.linearMapAt ℝ (trivializationAt E (TangentSpace I) x₁) p)
      ((trivializationAt E (TangentSpace I) x₀).symm p ((Module.finBasis ℝ E) a)))) c

/-- On the base set, the `linearMapAt` of the trivialisation at `x₁`, applied to the `symm` of the
trivialisation at `x₀`, is the change of fibre coordinates `coordChangeL`. -/
lemma linearMapAt_symm_eq_coordChangeL (x₀ x₁ p : M)
    (hp₀ : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hp₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) (v : E) :
    (Trivialization.linearMapAt ℝ (trivializationAt E (TangentSpace I) x₁) p)
        ((trivializationAt E (TangentSpace I) x₀).symm p v)
      = (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) x₀)
          (trivializationAt E (TangentSpace I) x₁) p) v := by
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₁).baseSet := ⟨hp₀, hp₁⟩
  rw [Trivialization.coordChangeL_apply _ _ hb, Trivialization.linearMapAt_def_of_mem _ hp₁]
  exact Trivialization.linearEquivAt_apply (trivializationAt E (TangentSpace I) x₁) p hp₁ _

/-- The change of fibre coordinates of the tangent bundle is the chart transition
`tangentCoordChange`. -/
lemma coordChangeL_eq_tangentCoordChange (x₀ x₁ p : M)
    (hbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₁).baseSet) (v : E) :
    (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) x₀)
      (trivializationAt E (TangentSpace I) x₁) p) v = tangentCoordChange (I := I) x₀ x₁ p v := by
  have h := VectorBundleCore.trivializationAt_coordChange_eq (tangentBundleCore I M)
    (b₀ := x₀) (b₁ := x₁) (b := p) hbase v
  rw [tangentCoordChange]
  exact h

/-- The coefficient matrix of the change of frame is the transpose of the matrix of the change of
fibre coordinates in the canonical basis of the model space. -/
lemma chartCoeffMat_eq_transpose (x₀ x₁ p : M)
    (hp₀ : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hp₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartCoeffMat (I := I) x₀ x₁ p
      = (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
          ((Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) x₀)
            (trivializationAt E (TangentSpace I) x₁) p : E →ₗ[ℝ] E)))ᵀ := by
  ext a c
  rw [chartCoeffMat, Matrix.transpose_apply, LinearMap.toMatrix_apply]
  exact congrArg (fun w => (Module.finBasis ℝ E).repr w c)
    (linearMapAt_symm_eq_coordChangeL (I := I) x₀ x₁ p hp₀ hp₁ (Module.finBasis ℝ E a))

/-- **The determinant of the change of trivialisation frame is the determinant of the chart
transition** `tangentCoordChange`. -/
lemma det_chartCoeffMat (x₀ x₁ p : M)
    (hp₀ : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hp₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (chartCoeffMat (I := I) x₀ x₁ p).det = (tangentCoordChange (I := I) x₀ x₁ p).det := by
  rw [chartCoeffMat_eq_transpose (I := I) x₀ x₁ p hp₀ hp₁, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  congr 1
  refine LinearMap.ext (fun v => ?_)
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₁).baseSet := ⟨hp₀, hp₁⟩
  show (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) x₀)
      (trivializationAt E (TangentSpace I) x₁) p) v = tangentCoordChange (I := I) x₀ x₁ p v
  exact coordChangeL_eq_tangentCoordChange (I := I) x₀ x₁ p hb v

/-- The entrywise form of the matrix product `A * G * Aᵀ`. -/
lemma mul_transpose_apply {n : Type*} [Fintype n] [DecidableEq n]
    (A G : Matrix n n ℝ) (a b : n) :
    (A * G * Aᵀ) a b = ∑ c, ∑ d, (A a c * A b d) * G c d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by ring))

/-- **The gauge formula for the chart matrices of the metric.**  On the overlap of the charts at
`x₀` and `x₁`, the chart matrix in the chart at `x₀` is obtained from the chart matrix in the chart
at `x₁` by the matrix of the change of trivialisation frame. -/
lemma chartMatFun_mul (g : Submission.Diff.SMet I M) (x₀ x₁ p : M)
    (hsrc₀ : p ∈ (extChartAt I x₀).source)
    (hsrc₁ : p ∈ (extChartAt I x₁).source) :
    Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) p))
      = chartCoeffMat (I := I) x₀ x₁ p
        * Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₁ ((extChartAt I x₁) p))
        * (chartCoeffMat (I := I) x₀ x₁ p)ᵀ := by
  have hb₀ : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hsrc₀
  have hb₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hsrc₁
  have hsp₀ : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hsrc₀
  have hsp₁ : (extChartAt I x₁).symm ((extChartAt I x₁) p) = p := (extChartAt I x₁).left_inv hsrc₁
  ext a b
  rw [mul_transpose_apply]
  have hbc := Work.Diff.STE.fill.bilChart_change (I := I) (M := M)
    (h := fun x => g.inner x) x₀ x₁ p hb₀ hb₁ a b
  simp only [Matrix.of_apply, Work.Diff.EXT.chartMatFun, Work.Diff.STE.bilChart, chartCoeffMat]
    at hbc ⊢
  rw [hsp₀, hsp₁] at hbc
  rw [hsp₀, hsp₁]
  exact hbc

/-- **The determinant of the gauge formula.**  The determinant of the chart matrix transforms by the
square of the determinant of the change of frame. -/
lemma det_chartMatFun_mul (g : Submission.Diff.SMet I M) (x₀ x₁ p : M)
    (hsrc₀ : p ∈ (extChartAt I x₀).source)
    (hsrc₁ : p ∈ (extChartAt I x₁).source) :
    Matrix.det (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) p)))
      = (Matrix.det (chartCoeffMat (I := I) x₀ x₁ p)) ^ 2
        * Matrix.det (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₁
            ((extChartAt I x₁) p))) := by
  rw [chartMatFun_mul (I := I) g x₀ x₁ p hsrc₀ hsrc₁,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end Helpers

theorem dens_transition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) (p : M)
    (hi : p ∈ (extChartAt I (D.x₀ i)).source)
    (hj : p ∈ (extChartAt I (D.x₀ j)).source) :
    D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
      = |(tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) p).det|
          * D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) := by
  classical
  have hb0 : p ∈ (trivializationAt E (TangentSpace I) (D.x₀ i)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hi
  have hb1 : p ∈ (trivializationAt E (TangentSpace I) (D.x₀ j)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hj
  rw [Work.Diff.STE.B3Data.dens, flatToE_coord (I := I) (D.x₀ i) p,
    Work.Diff.STE.B3Data.dens, flatToE_coord (I := I) (D.x₀ j) p]
  rw [det_chartMatFun_mul (I := I) g₀ (D.x₀ i) (D.x₀ j) p hi hj,
    Real.sqrt_mul (sq_nonneg (Matrix.det (chartCoeffMat (I := I) (D.x₀ i) (D.x₀ j) p))),
    Real.sqrt_sq_eq_abs, det_chartCoeffMat (I := I) (D.x₀ i) (D.x₀ j) p hb0 hb1]

end Work.Diff.STE.B3
