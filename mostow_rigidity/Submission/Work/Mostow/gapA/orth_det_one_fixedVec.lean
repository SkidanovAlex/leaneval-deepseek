import Mathlib

/-!
# A special-orthogonal `3 × 3` real matrix fixes a nonzero vector

Every `S ∈ SO(3)` is a rotation about an axis, hence has a fixed vector.  The formal proof
avoids eigenvalues entirely: for an orthogonal `S` with `det S = 1` in odd dimension one has

`det (S - 1) = det (Sᵀ (S - 1)) = det (1 - Sᵀ) = det ((1 - Sᵀ)ᵀ) = det (1 - S) = - det (S - 1)`,

because `det Sᵀ = det S = 1` and `1 - S = -(S - 1)` with `(-1) ^ 3 = -1`.  Hence `det (S - 1) = 0`
and a nonzero kernel vector `x` of `S - 1` satisfies `S x = x`.
-/

namespace Work.Mostow.gapA

/-- A `3 × 3` real special-orthogonal matrix has a nonzero fixed vector. -/
theorem orth_det_one_fixedVec (S : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : S.transpose * S = 1) (hdet : S.det = 1) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ Matrix.mulVec S x = x := by
  -- `1` is an eigenvalue: `det (S - 1) = 0`.
  have hdet0 : (S - 1).det = 0 := by
    have hchain : (S - 1).det = - (S - 1).det := by
      calc (S - 1).det = (S.transpose * (S - 1)).det := by
                rw [Matrix.det_mul, Matrix.det_transpose, hdet, one_mul]
        _ = (1 - S.transpose).det := by
              rw [Matrix.mul_sub, Matrix.mul_one, horth]
        _ = (1 - S).det := by
              rw [(Matrix.det_transpose (1 - S.transpose)).symm]
              congr 1
              rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
        _ = (-(S - 1)).det := by rw [(neg_sub S 1).symm]
        _ = - (S - 1).det := by
              rw [Matrix.det_neg, Fintype.card_fin]
              ring
    linarith
  -- Singularity gives a nonzero vector killed by `S - 1`, i.e. fixed by `S`.
  obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  refine ⟨v, hvne, ?_⟩
  have hsub : Matrix.mulVec (S - 1) v = Matrix.mulVec S v - v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hsub] at hv0
  exact sub_eq_zero.mp hv0

end Work.Mostow.gapA
