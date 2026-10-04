import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

/-- Spectral theorem for real symmetric matrices: a symmetric matrix admits an orthonormal
eigenbasis.  Concretely, there are vectors `f · j` (the columns of `f`) forming an orthonormal
family and numbers `mu j` such that `M *ᵥ (f · j) = mu j • (f · j)`, i.e.
`∑ k, M i k * f k j = mu j * f i j`. -/
theorem exists_orthonormal_eigenbasis (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) :
    ∃ (f : Fin n → Fin n → ℝ) (mu : Fin n → ℝ),
      (∀ i j, ∑ k, f k i * f k j = if i = j then 1 else 0) ∧
      (∀ j, ∀ i, ∑ k, M i k * f k j = mu j * f i j) := by
  classical
  -- A real symmetric matrix is Hermitian (star is trivial on `ℝ`).
  have hHerm : M.IsHermitian := Matrix.IsHermitian.ext (fun i j => by simpa using hM j i)
  -- Take the orthonormal eigenbasis of `M`, and its real eigenvalues.
  refine ⟨fun k j => (hHerm.eigenvectorBasis j).ofLp k, fun j => hHerm.eigenvalues j, ?_, ?_⟩
  · -- Orthonormality of the columns, from the inner product on `EuclideanSpace ℝ (Fin n)`.
    intro i j
    have h := (orthonormal_iff_ite.mp hHerm.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, star_trivial, eq_comm] using h
  · -- Eigenvector equation, from `Matrix.IsHermitian.mulVec_eigenvectorBasis`.
    intro j i
    have h := congr_fun (hHerm.mulVec_eigenvectorBasis j) i
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using h

end Work.Diff.Alg.Pinch
