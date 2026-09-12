import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_pow_idealOfVars_le_of_homogeneousComponent_mem

namespace Commons.Algebra.MvPolynomial

theorem homogeneous_isHomogeneous_mem_of_finite_quotient {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : ∀ (j : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ p : MvPolynomial (Fin n) ℂ, p.IsHomogeneous j → p ∈ I := by
  obtain ⟨N, hN⟩ :=
    exists_pow_idealOfVars_le_of_homogeneousComponent_mem I hI hfin
  refine ⟨N, fun j hj p hp => ?_⟩
  apply hN
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  exact hp.coeff_eq_zero (by omega)

end Commons.Algebra.MvPolynomial
