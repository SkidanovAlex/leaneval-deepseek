import Mathlib.Algebra.Polynomial.Coeff

namespace Commons.Algebra.Polynomial

theorem coeff_sum_monomial {A : Type*} [CommRing A] {n : ℕ} (c : Fin n → A) (k : ℕ) :
    (∑ b : Fin n, Polynomial.monomial (b : ℕ) (c b)).coeff k
      = if h : k < n then c ⟨k, h⟩ else 0 := by
  rw [Polynomial.finsetSum_coeff]
  by_cases h : k < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [Polynomial.coeff_monomial]
      exact if_neg (fun hbk => hb (Fin.ext hbk))
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [dif_neg h, Finset.sum_eq_zero]
    intro b _
    rw [Polynomial.coeff_monomial]
    exact if_neg (fun hbk => h (by rw [← hbk]; exact b.isLt))

end Commons.Algebra.Polynomial