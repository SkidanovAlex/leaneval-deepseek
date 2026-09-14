import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal

open scoped BigOperators

namespace Commons.LinearAlgebra.GramMatrix

theorem gram_change_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : ι → E) (A : Matrix ι ι ℤ)
    (hfe : ∀ j : ι, f j = ∑ i : ι, (A j i : ℝ) • e i) :
    (Matrix.gram ℝ f).det =
      ((A.map (fun z : ℤ => (z : ℝ))).det) ^ 2 * (Matrix.gram ℝ e).det := by
  let M : Matrix ι ι ℝ := A.map (fun z : ℤ => (z : ℝ))
  have hM : ∀ j : ι, f j = ∑ i : ι, M j i • e i := by
    intro j
    simpa [M] using hfe j
  have hgram : Matrix.gram ℝ f = M * Matrix.gram ℝ e * M.transpose := by
    calc
      Matrix.gram ℝ f = Matrix.gram ℝ (fun a : ι => ∑ b : ι, M a b • e b) := by
        congr 1
        funext a
        exact hM a
      _ = M * Matrix.gram ℝ e * M.transpose :=
        Commons.Analysis.InnerProductSpace.gram_eq_mul_gram_mul_transpose M e
  calc
    (Matrix.gram ℝ f).det = (M * Matrix.gram ℝ e * M.transpose).det := by rw [hgram]
    _ = M.det ^ 2 * (Matrix.gram ℝ e).det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    _ = ((A.map (fun z : ℤ => (z : ℝ))).det) ^ 2 * (Matrix.gram ℝ e).det := by
      simp [M]

end Commons.LinearAlgebra.GramMatrix
