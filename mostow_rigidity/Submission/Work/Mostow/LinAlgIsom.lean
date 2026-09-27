import Mathlib
import Submission.Work.Mostow.BCGDefs

/-!
# A linear map with `‖A v‖ ≤ ‖v‖` and `|det A| = 1` is an isometry

Let `E` be a finite dimensional real inner product space and `A : E →ₗ[ℝ] E` a linear
endomorphism that is a contraction (`‖A v‖ ≤ ‖v‖` for all `v`) whose determinant has
absolute value `1`.  Then `A` preserves the inner product, i.e. it is orthogonal.

This is the linear-algebraic fact behind the algebraic form of Mostow rigidity: a
volume-preserving (`|det A| = 1`) contraction on the tangent space is an isometry.

## Proof

Consider the positive semidefinite self-adjoint operator `S = A* ∘ A`, so that
`⟪A v, A w⟫ = ⟪v, S w⟫`.  In an orthonormal eigenbasis of `S` with eigenvalues `λ i`,
the hypothesis gives `0 ≤ λ i = ‖A b i‖² ≤ ‖b i‖² = 1`, while
`∏ i, λ i = det S = det(A*) · det A = (det A)² = 1`.  A product of numbers in `[0,1]`
equal to `1` forces every factor to be `1`, so `S = id` and `A` is an isometry.
-/

namespace Work.Mostow

theorem LinAlgIsom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) (h : ∀ v, ‖A v‖ ≤ ‖v‖) (hdet : |A.det| = 1) :
    ∀ v w : E, inner ℝ (A v) (A w) = inner ℝ v w := by
  -- the determinant is invariant under taking the adjoint
  have hdet_adj : (LinearMap.adjoint A).det = A.det := by
    let b := stdOrthonormalBasis ℝ E
    rw [← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint A),
        ← LinearMap.det_toMatrix b.toBasis A,
        LinearMap.toMatrix_adjoint b b A, Matrix.det_conjTranspose]
    simp
  let S := A.adjoint.comp A
  let n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  -- `S` is self-adjoint
  have hsym : S.IsSymmetric := by
    intro x y
    change inner ℝ (A.adjoint (A x)) y = inner ℝ x (A.adjoint (A y))
    rw [LinearMap.adjoint_inner_left A y (A x), LinearMap.adjoint_inner_right A x (A y)]
  -- the eigenvalues are the diagonal values `⟪S b i, b i⟫`
  have heig : ∀ i : Fin n,
      hsym.eigenvalues hn i
        = inner ℝ (S (hsym.eigenvectorBasis hn i)) (hsym.eigenvectorBasis hn i) := by
    intro i
    rw [hsym.apply_eigenvectorBasis hn i, real_inner_smul_left,
        (hsym.eigenvectorBasis hn).inner_eq_ite i i, ite_eq_left rfl, mul_one]
    simp
  -- the eigenvalues are nonnegative and at most one
  have h0 : ∀ i : Fin n, 0 ≤ hsym.eigenvalues hn i := by
    intro i
    rw [heig i]
    change 0 ≤ inner ℝ (A.adjoint (A (hsym.eigenvectorBasis hn i)))
        (hsym.eigenvectorBasis hn i)
    rw [LinearMap.adjoint_inner_left A (hsym.eigenvectorBasis hn i)
        (A (hsym.eigenvectorBasis hn i)), real_inner_self_eq_norm_sq]
    positivity
  have h1 : ∀ i : Fin n, hsym.eigenvalues hn i ≤ 1 := by
    intro i
    rw [heig i]
    change inner ℝ (A.adjoint (A (hsym.eigenvectorBasis hn i)))
        (hsym.eigenvectorBasis hn i) ≤ 1
    rw [LinearMap.adjoint_inner_left A (hsym.eigenvectorBasis hn i)
        (A (hsym.eigenvectorBasis hn i)), real_inner_self_eq_norm_sq]
    have hb : ‖hsym.eigenvectorBasis hn i‖ = 1 := (hsym.eigenvectorBasis hn).norm_eq_one i
    have h2 := h (hsym.eigenvectorBasis hn i)
    rw [hb] at h2
    calc ‖A (hsym.eigenvectorBasis hn i)‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 1 := by norm_num
  -- the determinant of `S` is one
  have hdetS : LinearMap.det S = 1 := by
    change LinearMap.det (A.adjoint ∘ₗ A) = 1
    rw [LinearMap.det_comp, hdet_adj]
    have hsq : A.det ^ 2 = 1 := by rw [← sq_abs, hdet]; norm_num
    simpa [pow_two] using hsq
  -- hence the product of the eigenvalues is one
  have hprod : ∏ i : Fin n, hsym.eigenvalues hn i = 1 := by
    have hh := hsym.det_eq_prod_eigenvalues (𝕜 := ℝ) hn
    rw [hdetS] at hh
    simpa using hh.symm
  -- a product of numbers in `[0,1]` equal to `1` has every factor equal to `1`
  have hone : ∀ i : Fin n, hsym.eigenvalues hn i = 1 := by
    intro j
    refine le_antisymm (h1 j) ?_
    have hsplit : ∏ i : Fin n, hsym.eigenvalues hn i
        = hsym.eigenvalues hn j * ∏ i ∈ Finset.univ.erase j, hsym.eigenvalues hn i :=
      (Finset.mul_prod_erase Finset.univ (fun i => hsym.eigenvalues hn i)
        (Finset.mem_univ j)).symm
    have hrest : ∏ i ∈ Finset.univ.erase j, hsym.eigenvalues hn i ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => h0 i) (fun i _ => h1 i)
    calc (1:ℝ) = ∏ i : Fin n, hsym.eigenvalues hn i := hprod.symm
      _ = hsym.eigenvalues hn j * ∏ i ∈ Finset.univ.erase j, hsym.eigenvalues hn i := hsplit
      _ ≤ hsym.eigenvalues hn j := mul_le_of_le_one_right (h0 j) hrest
  -- so `S` acts as the identity on an orthonormal basis, hence `S = 1`
  have hSone : S = 1 := by
    apply Module.Basis.ext (hsym.eigenvectorBasis hn).toBasis
    intro i
    change S (hsym.eigenvectorBasis hn i) = (1 : E →ₗ[ℝ] E) (hsym.eigenvectorBasis hn i)
    rw [hsym.apply_eigenvectorBasis hn i, hone i]
    simp
  intro v w
  have h1' : inner ℝ (A v) (A w) = inner ℝ v (S w) := by
    change inner ℝ (A v) (A w) = inner ℝ v (A.adjoint (A w))
    rw [LinearMap.adjoint_inner_right A v (A w)]
  rw [h1', hSone]
  simp

end Work.Mostow
