import Mathlib.Analysis.Matrix.Spectrum

namespace Commons.Analysis.Matrix

open _root_.Matrix Polynomial

/-- For a real Hermitian matrix `M`, the determinant of `c • 1 + M` equals the product of
`c + λ` over the eigenvalues `λ` of `M`. -/
theorem det_add_smul_one_eq_prod_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) (c : ℝ) :
    (c • 1 + M).det = ∏ i, (c + hM.eigenvalues i) := by
  have hN : (c • 1 + M).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hM.eq]
    simp
  have h1 : (c • 1 + M : Matrix n n ℝ) = M - scalar n (-c) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply]; ring
    · simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, hij]
  have hchar : (c • 1 + M).charpoly = ∏ i, (X - C (c + hM.eigenvalues i)) := by
    rw [h1, Matrix.charpoly_sub_scalar, hM.charpoly_eq, Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      RCLike.ofReal_real_eq_id, id_eq, Polynomial.C_neg, Polynomial.C_add]
    ring
  calc (c • 1 + M).det
      = (c • 1 + M).charpoly.roots.prod :=
          Matrix.det_eq_prod_roots_charpoly_of_splits hN.splits_charpoly
    _ = (Finset.univ.val.map fun i => c + hM.eigenvalues i).prod := by
          rw [hchar, Polynomial.roots_prod]
          · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
          · rw [Finset.prod_ne_zero_iff]
            intro i _
            exact Polynomial.X_sub_C_ne_zero _
    _ = ∏ i, (c + hM.eigenvalues i) := by rw [Finset.prod_eq_multiset_prod]

end Commons.Analysis.Matrix