import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Commons.Algebra.MvPolynomial

/-- The formal partial derivative does not increase the total degree. -/
theorem totalDegree_pderiv_le {σ : Type*} {R : Type*} [CommSemiring R] (f : MvPolynomial σ R)
    (j : σ) : (MvPolynomial.pderiv j f).totalDegree ≤ f.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree]
  refine Finset.sup_le fun m hm => ?_
  rw [MvPolynomial.mem_support_iff] at hm
  rw [MvPolynomial.coeff_pderiv] at hm
  have hm' : MvPolynomial.coeff (m + Finsupp.single j 1) f ≠ 0 :=
    fun h => hm (by rw [h, zero_mul])
  refine (Finsupp.sum_le_sum_index (f₁ := m) (f₂ := m + Finsupp.single j 1)
    (h := fun _ e => e) ?_ ?_ ?_).trans ?_
  · exact le_add_of_nonneg_right (Finsupp.single_nonneg.mpr (Nat.zero_le 1))
  · exact fun i _ => monotone_id
  · exact fun i _ => rfl
  · exact MvPolynomial.le_totalDegree (by rwa [MvPolynomial.mem_support_iff])

end Commons.Algebra.MvPolynomial