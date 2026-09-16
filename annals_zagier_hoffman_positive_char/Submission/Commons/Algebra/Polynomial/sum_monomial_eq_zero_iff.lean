import Mathlib.Algebra.Polynomial.Coeff

namespace Commons.Algebra.Polynomial


theorem sum_monomial_eq_zero_iff {A : Type*} [CommRing A] {n : ℕ} (c : Fin n → A) :
    (∑ b : Fin n, Polynomial.monomial (b : ℕ) (c b)) = 0 ↔ ∀ b, c b = 0 := by
  constructor
  · intro h b
    have hb : (∑ x : Fin n, (Polynomial.monomial (x : ℕ) (c x)).coeff b) = 0 := by
      have := congrArg (fun p : Polynomial A => p.coeff b) h
      simpa using this
    rw [Finset.sum_eq_single b
        (fun i _ hi => by
          rw [Polynomial.coeff_monomial]
          exact if_neg (fun hik => hi (Fin.ext hik)))
        (fun hnot => absurd (Finset.mem_univ b) hnot)] at hb
    rwa [Polynomial.coeff_monomial_same] at hb
  · intro h
    simp [h]

end Commons.Algebra.Polynomial