import Mathlib

open scoped ComplexOrder

namespace Work.Avalanche

/-- If `X` is a complex matrix with determinant `1`, then the Gram matrix `Xᴴ * X` can be
diagonalized by a unitary `V` with a positive real diagonal `d` whose product is `1`. -/
lemma gram_spectral_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.det = 1) :
    ∃ (V : Matrix n n ℂ) (d : n → ℝ),
      V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1 ∧
      (∀ i, 0 < d i) ∧ (∏ i, d i) = 1 ∧
      X.conjTranspose * X = V * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * V.conjTranspose := by
  have h := Matrix.isHermitian_conjTranspose_mul_self X
  have hpd : (X.conjTranspose * X).PosDef := by
    exact Matrix.PosDef.conjTranspose_mul_self X (by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hX]
      exact isUnit_one)
  have hdet : (X.conjTranspose * X).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, hX]; simp
  have key : (X.conjTranspose * X).det = ∏ i, (h.eigenvalues i : ℂ) :=
    h.det_eq_prod_eigenvalues
  have hprodC : ∏ i, (h.eigenvalues i : ℂ) = 1 := by
    rw [← key, hdet]
  have hprodR : ∏ i, h.eigenvalues i = 1 := by
    apply Complex.ofReal_injective
    have e1 : ((∏ i, h.eigenvalues i : ℝ) : ℂ) = ∏ i, (h.eigenvalues i : ℂ) :=
      map_prod Complex.ofRealHom h.eigenvalues Finset.univ
    rw [e1, hprodC]; norm_num
  have hspec' :
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues)) =
        (h.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (fun i => ((h.eigenvalues i : ℝ) : ℂ)) *
          (h.eigenvectorUnitary : Matrix n n ℂ).conjTranspose := by
    rw [Unitary.conjStarAlgAut_apply]; rfl
  refine ⟨(h.eigenvectorUnitary : Matrix n n ℂ), h.eigenvalues, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self h.eigenvectorUnitary
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self h.eigenvectorUnitary
  · intro i
    exact (h.posDef_iff_eigenvalues_pos).mp hpd i
  · exact hprodR
  · exact h.spectral_theorem.trans hspec'

end Work.Avalanche
