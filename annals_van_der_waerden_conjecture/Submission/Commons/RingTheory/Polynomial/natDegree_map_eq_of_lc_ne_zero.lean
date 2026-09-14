import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Polynomial

namespace Commons.RingTheory.Polynomial

theorem natDegree_map_eq_of_lc_ne_zero {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    {p : R[X]} (hφ : φ (p.leadingCoeff) ≠ 0) : (p.map φ).natDegree = p.natDegree := by
  exact (Polynomial.natDegree_map_eq_iff.mpr (Or.inl hφ))

end Commons.RingTheory.Polynomial