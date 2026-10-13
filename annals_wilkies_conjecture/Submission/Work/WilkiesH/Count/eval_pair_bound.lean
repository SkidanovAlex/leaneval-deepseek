import Mathlib

namespace Work.WilkiesH.Count

/-- For a bivariate polynomial, the exponent of the first variable in a monomial
of the support is bounded by the total degree. -/
lemma fst_le_totalDegree {b : MvPolynomial (Fin 2) ℕ} {d : Fin 2 →₀ ℕ}
    (hd : d ∈ b.support) : d 0 ≤ b.totalDegree := by
  have h1 : d 0 ≤ d.sum (fun _ e => e) := by
    by_cases h : (0 : Fin 2) ∈ d.support
    · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) h
    · rw [Finsupp.mem_support_iff, not_not] at h
      rw [h]; exact Nat.zero_le _
  exact le_trans h1 (MvPolynomial.le_totalDegree hd)

/-- Evaluation of a bivariate polynomial at `(D, 1)`: since the second variable is
set to `1`, only the exponent of the first variable survives. -/
lemma eval_pair_eq (b : MvPolynomial (Fin 2) ℕ) (D : ℕ) :
    MvPolynomial.eval ![D, 1] b = ∑ d ∈ b.support, b.coeff d * D ^ (d 0) := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [Fin.prod_univ_two]
  simp

/-- Evaluation at `(D, 1)` is bounded by the sum of the coefficients times
`(D + 1)` to the total degree: each monomial of the support contributes
`coeff * D ^ (d 0) ≤ coeff * (D + 1) ^ totalDegree`. -/
lemma eval_pair_bound (b : MvPolynomial (Fin 2) ℕ) (D : ℕ) :
    MvPolynomial.eval ![D, 1] b ≤ (b.support.sum b.coeff) * (D + 1) ^ b.totalDegree := by
  rw [eval_pair_eq]
  calc ∑ d ∈ b.support, b.coeff d * D ^ (d 0)
      ≤ ∑ d ∈ b.support, b.coeff d * (D + 1) ^ b.totalDegree := by
        apply Finset.sum_le_sum
        intro d hd
        exact Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left (Nat.le_succ D) (d 0))
          (Nat.pow_le_pow_right (Nat.succ_pos D) (fst_le_totalDegree hd)))
    _ = (b.support.sum b.coeff) * (D + 1) ^ b.totalDegree := by
        rw [Finset.sum_mul]

end Work.WilkiesH.Count
