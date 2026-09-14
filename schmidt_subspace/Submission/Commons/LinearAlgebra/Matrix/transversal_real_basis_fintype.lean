import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.transversal_real_basis

namespace Commons.LinearAlgebra.Matrix

/-- **Transversal real basis, arbitrary finite index type.**

Given an invertible complex `ι × ι` matrix `L` (with `ι` a finite type), one can select,
independently for every row, either the real part or the imaginary part of that row so that
the resulting *real* matrix is again invertible.

This is deduced from the `Fin N` version `Commons.LinearAlgebra.Matrix.transversal_real_basis`
by reindexing along an equivalence `ι ≃ Fin (Fintype.card ι)`; the determinant is invariant
under `Matrix.reindex e e` (`Matrix.det_reindex_self`). -/
theorem transversal_real_basis_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ι → ℂ)
    (hdet : (Matrix.of L).det ≠ 0) :
    ∃ s : ι → Fin 2,
      (Matrix.of (fun i k => if s i = 0 then (L i k).re else (L i k).im)).det ≠ 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let L' : Fin (Fintype.card ι) → Fin (Fintype.card ι) → ℂ :=
    fun a b => L (e.symm a) (e.symm b)
  have hL' : (Matrix.of L').det ≠ 0 := by
    have h1 : Matrix.of L' = (Matrix.reindex e e) (Matrix.of L) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, L']
    rw [h1, Matrix.det_reindex_self]
    exact hdet
  obtain ⟨s', hs'⟩ := transversal_real_basis L' hL'
  refine ⟨fun i => s' (e i), ?_⟩
  set M' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    Matrix.of (fun a b => if s' a = 0 then (L' a b).re else (L' a b).im) with hM'
  set M : Matrix ι ι ℝ :=
    Matrix.of (fun i k => if s' (e i) = 0 then (L i k).re else (L i k).im) with hM
  have hmat : M' = (Matrix.reindex e e) M := by
    ext a b
    simp only [hM', hM, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, L',
      Equiv.apply_symm_apply]
  have hdet_eq : M'.det = M.det := by
    rw [hmat, Matrix.det_reindex_self]
  rw [← hdet_eq]
  exact hs'

end Commons.LinearAlgebra.Matrix

