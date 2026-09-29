import Mathlib

namespace Work.ZeroEst

/-- The determinant of an `m × m` matrix of polynomials each of `natDegree ≤ N` has
`natDegree ≤ m * N`.  Via the Leibniz formula: `det M = ∑ σ, sign σ • ∏ i, M (σ i) i`,
each summand is a product of `m` entries of degree `≤ N`, and a finite sum of polynomials
of degree `≤ m * N` again has degree `≤ m * N`. -/
theorem case_det_detdeg {m : ℕ} (M : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (N : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ N) : M.det.natDegree ≤ m * N := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  refine (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc ∑ i ∈ Finset.univ, (M (σ i) i).natDegree
      ≤ ∑ i ∈ Finset.univ, N := Finset.sum_le_sum (fun i _ => h (σ i) i)
    _ = m * N := by simp [Finset.sum_const, Finset.card_univ]

end Work.ZeroEst
