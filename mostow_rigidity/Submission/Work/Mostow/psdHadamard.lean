import Mathlib
import Submission.Work.Mostow.psdDiagOneDetLeOne

namespace Work.Mostow

/-- For a positive semidefinite real matrix, a vanishing diagonal entry forces the whole
corresponding column to vanish (via `x ⋆ A x = 0 ↔ A x = 0` for `x` a standard basis
vector), hence the determinant is zero. -/
lemma det_eq_zero_of_diag_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) (i : n) (h : A i i = 0) : A.det = 0 := by
  have hz : dotProduct (star (Pi.single i (1:ℝ))) (Matrix.mulVec A (Pi.single i (1:ℝ))) = 0 := by
    simp [h]
  have hv := (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA).mp hz
  refine Matrix.det_eq_zero_of_column_eq_zero i (fun j => ?_)
  have := congrFun hv j
  simpa [Matrix.mulVec, Pi.single_eq_same, Pi.single_eq_of_ne] using this

/-- **Hadamard's inequality** for positive semidefinite real matrices:
`det A ≤ ∏ i, A i i`.

Proof: if some diagonal entry vanishes, that column is zero and `det A = 0 ≤ ∏ i, A i i`.
Otherwise all diagonal entries are positive, and conjugating by the diagonal matrix
`s i = (√(A i i))⁻¹` produces a positive semidefinite matrix `B = D A D` with unit
diagonal and `A.det = (∏ i, A i i) * B.det`. Since a unit-diagonal PSD matrix has
determinant at most `1` (AM–GM applied to the nonnegative eigenvalues, whose sum is the
trace), the claim follows. -/
theorem psdHadamard {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i := by
  classical
  by_cases hcard0 : Fintype.card n = 0
  · rw [Matrix.det_eq_one_of_card_eq_zero hcard0]
    have hIns : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard0
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  · by_cases hz0 : ∃ i, A i i = 0
    · obtain ⟨i, hi⟩ := hz0
      rw [det_eq_zero_of_diag_eq_zero A hA i hi]
      exact Finset.prod_nonneg (fun i _ => hA.diag_nonneg)
    · have hpos : ∀ i, 0 < A i i := by
        intro i
        rcases lt_or_eq_of_le hA.diag_nonneg with h | h
        · exact h
        · exact absurd ⟨i, h.symm⟩ hz0
      let s : n → ℝ := fun i => (Real.sqrt (A i i))⁻¹
      have hs : ∀ i, s i * s i = (A i i)⁻¹ := by
        intro i
        show ((Real.sqrt (A i i))⁻¹) * ((Real.sqrt (A i i))⁻¹) = (A i i)⁻¹
        rw [← mul_inv, ← sq, Real.sq_sqrt (le_of_lt (hpos i))]
      have hBpsd : (Matrix.diagonal s * A * Matrix.diagonal s).PosSemidef := by
        have := hA.mul_mul_conjTranspose_same (Matrix.diagonal s)
        simpa [Matrix.diagonal_conjTranspose] using this
      have hBdiag : ∀ i, (Matrix.diagonal s * A * Matrix.diagonal s) i i = 1 := by
        intro i
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
        rw [show (s i * A i i) * s i = (s i * s i) * A i i by ring, hs i]
        exact inv_mul_cancel₀ (ne_of_gt (hpos i))
      have hdetB : (Matrix.diagonal s * A * Matrix.diagonal s).det
          = (∏ i, s i) * A.det * (∏ i, s i) := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      have hprod : (∏ i, s i) * (∏ i, s i) = (∏ i, A i i)⁻¹ := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl (fun i _ => hs i)
      have hdetA : A.det = (∏ i, A i i) * (Matrix.diagonal s * A * Matrix.diagonal s).det := by
        have hBd : (Matrix.diagonal s * A * Matrix.diagonal s).det = (∏ i, A i i)⁻¹ * A.det := by
          rw [hdetB]
          rw [show (∏ i, s i) * A.det * (∏ i, s i)
              = ((∏ i, s i) * (∏ i, s i)) * A.det by ring, hprod]
        rw [hBd, ← mul_assoc,
          mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hpos i))), one_mul]
      rw [hdetA]
      exact mul_le_of_le_one_right (Finset.prod_nonneg (fun i _ => le_of_lt (hpos i)))
        (psdDiagOneDetLeOne _ hBpsd hBdiag)

end Work.Mostow
