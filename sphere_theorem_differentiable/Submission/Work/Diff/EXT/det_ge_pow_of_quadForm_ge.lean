import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **A quadratic-form lower bound bounds the determinant.**  For a symmetric real matrix
`M : Matrix (Fin n) (Fin n) ℝ` with `ε * ∑ vᵢ² ≤ ∑ ᵢⱼ vᵢ vⱼ Mᵢⱼ` for every `v` and `0 < ε`, the
determinant is at least `ε ^ n`.

Proof: by the spectral theorem (`Matrix.IsHermitian.eigenvalues`, `det_eq_prod_eigenvalues` —
the latter is `Matrix.IsHermitian.det_eq_prod_eigenvalues` in this Mathlib) the determinant is the
product of the eigenvalues; for a unit eigenvector `v` with `M v = λ v` the hypothesis gives
`λ = ∑ᵢⱼ vᵢvⱼMᵢⱼ ≥ ε`, so `det M = ∏λᵢ ≥ ε ^ n`. -/
theorem det_ge_pow_of_quadForm_ge
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hsym : ∀ i j, M i j = M j i)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ v : Fin n → ℝ, ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * M i j) :
    ε ^ n ≤ M.det := by
  classical
  -- `M` is Hermitian (symmetric over `ℝ`), so it has an orthonormal eigenbasis.
  have hH : M.IsHermitian := Matrix.IsHermitian.ext (fun i j => by simpa using hsym j i)
  rw [hH.det_eq_prod_eigenvalues]
  -- Every eigenvalue is at least `ε`: test the hypothesis on a unit eigenvector.
  have key : ∀ i : Fin n, ε ≤ hH.eigenvalues i := by
    intro i
    set v : Fin n → ℝ := (hH.eigenvectorBasis i).ofLp with hv
    -- the eigenvector is a unit vector
    have hinner : inner ℝ (hH.eigenvectorBasis i) (hH.eigenvectorBasis i) = ∑ k, v k ^ 2 := by
      rw [hv, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, pow_two]
    have hnorm : ∑ k, v k ^ 2 = 1 := by
      rw [← hinner, real_inner_self_eq_norm_sq,
        hH.eigenvectorBasis.orthonormal.norm_eq_one i, one_pow]
    -- `M v = λ v`
    have hmv : ∀ k, Matrix.mulVec M v k = hH.eigenvalues i * v k := by
      intro k
      rw [hv, hH.mulVec_eigenvectorBasis i]
      simp
    -- the quadratic form of `M` on the eigenvector is the eigenvalue
    have hquad : ∑ k, ∑ j, v k * v j * M k j = hH.eigenvalues i * ∑ k, v k ^ 2 := by
      calc ∑ k, ∑ j, v k * v j * M k j
          = ∑ k, v k * (∑ j, M k j * v j) := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ k, v k * Matrix.mulVec M v k := by
            simp [Matrix.mulVec, dotProduct]
        _ = ∑ k, v k * (hH.eigenvalues i * v k) := by
            apply Finset.sum_congr rfl; intro k _; rw [hmv k]
        _ = hH.eigenvalues i * ∑ k, v k ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
    have h2 := h v
    rw [hquad, hnorm, mul_one, mul_one] at h2
    exact h2
  calc ε ^ n = ∏ _i : Fin n, ε := by simp
    _ ≤ ∏ i, hH.eigenvalues i :=
        Finset.prod_le_prod₀ (fun i _ => le_of_lt hε) (fun i _ => key i)

end Work.Diff.EXT
