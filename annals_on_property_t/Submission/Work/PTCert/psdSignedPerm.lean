import Mathlib
import Submission.Work.PTCert.Chain

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Chain.lean` (also Math.lean, Interfaces.lean).
Prove `PSDSignedPerm`: `M' = D Pᵀ M P D` with `D = diagonal s` and `P` the permutation matrix of `τ`
(`Matrix.reindex`/`Matrix.submatrix M τ τ`), so `M'` is PSD by `Matrix.PosSemidef.submatrix` (PSD is preserved by
`submatrix` along an equiv) and `Matrix.PosSemidef.conjTranspose_mul_mul_same` / `mul_mul_conjTranspose_same`
with the (real, symmetric) diagonal matrix.  Or directly: `xᵀ M' x = (s∘x∘τ⁻¹)ᵀ M (…)`. ~50 lines.
-/

namespace Work.PTCert

open Submission.PTCert

/-- **(C3) PSD is invariant under signed permutation similarity.**

Writing `D` for the diagonal matrix of `s` and `τ` for the permutation (an equivalence of index
types), the matrix `M' x y = s x * s y * M (τ x) (τ y)` is exactly `D * (M.submatrix τ τ) * D`.
Since `M.submatrix τ τ` is a principal submatrix (along an equiv) of the positive semidefinite `M`,
it is positive semidefinite, and since `D` is diagonal it is symmetric (`Dᴴ = D`), so `M'` is a
conjugate `D * N * Dᴴ` of a PSD matrix, hence PSD.  In particular the hypothesis `s x = ±1` is not
needed: `M ↦ D M D` preserves positive semidefiniteness for any real diagonal `D`. -/
theorem psdSignedPerm : PSDSignedPerm := by
  classical
  intro ι κ _ _ M τ s _hs hM
  have hN : (M.submatrix τ τ).PosSemidef := hM.submatrix τ
  have hD : Matrix.conjTranspose (Matrix.diagonal s) = Matrix.diagonal s :=
    Matrix.isHermitian_diagonal s
  have key : (Matrix.diagonal s * (M.submatrix τ τ) * Matrix.diagonal s).PosSemidef := by
    have h := hN.conjTranspose_mul_mul_same (Matrix.diagonal s)
    rwa [hD] at h
  rw [show (Matrix.of fun x y => s x * s y * M (τ x) (τ y))
      = Matrix.diagonal s * (M.submatrix τ τ) * Matrix.diagonal s from ?_]
  exact key
  ext x y
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.submatrix]
  ring

end Work.PTCert
