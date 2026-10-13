import Mathlib

namespace Work.DSM2p

theorem N4c_coeff_sum_monomial_mul {C : Type*} [CommRing C] (p : ℕ) (hp : p.Prime)
    (s : Finset ℕ) (b : ℕ → C) (n : ℕ) :
    (∑ i ∈ s, Polynomial.monomial (i * p) (b i)).coeff (n * p)
      = if n ∈ s then b n else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, mul_left_inj' hp.ne_zero]
  exact Finset.sum_ite_eq' s n b

end Work.DSM2p
