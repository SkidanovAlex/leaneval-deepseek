import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped Polynomial

namespace Commons.FieldTheory.Polynomial

/-- For a finite field `F` and a natural number `N`, there are only finitely many
monic polynomials over `F` of natural degree strictly less than `N`. -/
theorem finite_monic_lt (F : Type*) [Field F] [Fintype F] (N : ℕ) :
    Finite {p : F[X] // p.Monic ∧ p.natDegree < N} := by
  -- A monic polynomial of natDegree < N is determined by its first N coefficients,
  -- each of which lives in the finite field F.
  refine Finite.of_injective
    (fun p : {p : F[X] // p.Monic ∧ p.natDegree < N} => fun i : Fin N => p.1.coeff (i : ℕ)) ?_
  rintro ⟨p, _hp_monic, hp_deg⟩ ⟨q, _hq_monic, hq_deg⟩ h
  apply Subtype.ext
  apply Polynomial.ext
  intro i
  by_cases hi : i < N
  · exact congr_fun h ⟨i, hi⟩
  · have hpdeg : p.natDegree < i := lt_of_lt_of_le hp_deg (le_of_not_gt hi)
    have hqdeg : q.natDegree < i := lt_of_lt_of_le hq_deg (le_of_not_gt hi)
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hpdeg,
      Polynomial.coeff_eq_zero_of_natDegree_lt hqdeg]

end Commons.FieldTheory.Polynomial