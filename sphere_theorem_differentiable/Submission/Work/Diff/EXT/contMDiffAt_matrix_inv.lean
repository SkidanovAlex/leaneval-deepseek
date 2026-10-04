import Mathlib
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the inverse of a jointly smooth invertible matrix family

The target lemma `Work.Diff.EXT.contMDiffAt_matrix_inv` says: if the entries of a matrix family
`Mx : ℝ × M → (Fin n → Fin n → ℝ)` are jointly `C^∞` near `(t₀, x)` and `Mx (t₀, x)` is invertible,
then the entries of the inverse family are jointly `C^∞` near `(t₀, x)`.

The work is done in the elementary setting of matrix-valued functions on `Fin n → Fin n → ℝ`
(which is definitionally `Matrix (Fin n) (Fin n) ℝ`).  Cramer's rule
`A⁻¹ = (A.det)⁻¹ • A.adjugate` (Mathlib's `Matrix.inv_def`) exhibits the entries of `A⁻¹` as
polynomial functions of the entries of `A` divided by the determinant, and every entry of the
adjugate is itself a determinant of a matrix with one row replaced
(`Matrix.adjugate_apply`).  Hence it suffices to know that

* `A ↦ A.det` is `C^∞` (a finite sum of finite products of coordinate functions),
* `A ↦ A.updateRow j b` is `C^∞` for a constant row `b`,
* and inversion of a nonvanishing scalar is `C^∞` (`ContDiffAt.inv`).

Composing the resulting `ContDiffAt` statement with `ContMDiffAt` (`ContDiffAt.comp_contMDiffAt`)
gives the lemma.
-/

open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.EXT

/-- The determinant of a matrix, as a function of its entries, is `C^∞`. -/
lemma contDiff_matrix_det_pi {n : ℕ} :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

/-- Replacing the `j`-th row of a matrix by a fixed row `b` is `C^∞` in the entries. -/
lemma contDiff_matrix_updateRow_pi {n : ℕ} (j : Fin n) (b : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => fun i l => ((Matrix.of A).updateRow j b) i l) := by
  simp only [Matrix.updateRow_apply, Matrix.of_apply]
  rw [contDiff_pi]; intro k; rw [contDiff_pi]; intro l
  by_cases h : k = j
  · simp only [h, ite_true]
    exact contDiff_const
  · simp only [h, ite_false]
    exact contDiff_apply_apply ℝ ℝ k l

/-- Every entry of the adjugate of a matrix is `C^∞` in the entries of the matrix. -/
lemma contDiff_matrix_adjugate_entry_pi {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).adjugate i j) := by
  have hrw : (fun A : Fin n → Fin n → ℝ => (Matrix.of A).adjugate i j)
      = fun A : Fin n → Fin n → ℝ => ((Matrix.of A).updateRow j (Pi.single i 1)).det := by
    funext A
    exact Matrix.adjugate_apply (Matrix.of A) i j
  rw [hrw]
  exact contDiff_matrix_det_pi.comp (contDiff_matrix_updateRow_pi j (Pi.single i 1))

/-- The entries of the inverse of an invertible matrix depend smoothly on the entries, near that
matrix. -/
lemma contDiffAt_matrix_inv_pi {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hM : (Matrix.of M).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun A : Fin n → Fin n → ℝ => fun i j => (Matrix.of A)⁻¹ i j) M := by
  have hdet : ContDiffAt ℝ ∞ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) M :=
    contDiff_matrix_det_pi.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun A : Fin n → Fin n → ℝ => ((Matrix.of A).det)⁻¹) M :=
    hdet.inv hM
  rw [contDiffAt_pi]; intro i
  rw [contDiffAt_pi]; intro j
  have hrw : (fun A : Fin n → Fin n → ℝ => (Matrix.of A)⁻¹ i j)
      = fun A => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    funext A
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact congrFun Ring.inverse_eq_inv' _
  rw [hrw]
  exact h1.mul (contDiff_matrix_adjugate_entry_pi i j).contDiffAt

/-- **Joint smoothness of the inverse of a jointly smooth invertible matrix family.**  If the
entries of `Mx : ℝ × M → (Fin n → Fin n → ℝ)` are jointly `C^∞` near `(t₀, x)` and the matrix
`Mx (t₀, x)` is invertible, then the entries of the inverse matrix are jointly `C^∞` near
`(t₀, x)`. -/
theorem contMDiffAt_matrix_inv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {n : ℕ} {Mx : ℝ × M → (Fin n → Fin n → ℝ)} {t₀ : ℝ} {x : M}
    (hM : JointSmoothAt I M Mx t₀ x) (hdet : (Matrix.of (Mx (t₀, x))).det ≠ 0) :
    JointSmoothAt I M (fun p i j => ((Matrix.of (Mx p))⁻¹) i j) t₀ x := by
  have hg : ContDiffAt ℝ ∞ (fun A : Fin n → Fin n → ℝ => fun i j => (Matrix.of A)⁻¹ i j)
      (Mx (t₀, x)) := contDiffAt_matrix_inv_pi (Mx (t₀, x)) hdet
  exact hg.comp_contMDiffAt hM

end Work.Diff.EXT
