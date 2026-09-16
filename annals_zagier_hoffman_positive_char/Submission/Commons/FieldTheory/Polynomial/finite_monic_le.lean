import Mathlib.Algebra.Polynomial.Degree.Operations

open Polynomial

namespace Commons.FieldTheory.Polynomial

/-- Monic polynomials over a finite field with degree at most `N` form a finite type:
a monic polynomial of degree `≤ N` is determined by its first `N + 1` coefficients,
each of which lies in the finite field `F`. -/
theorem finite_monic_le (F : Type*) [Field F] [Fintype F] (N : ℕ) :
    Finite {p : F[X] // p.Monic ∧ p.natDegree ≤ N} := by
  classical
  let cod := Fin (N + 1) → F
  let f : {p : F[X] // p.Monic ∧ p.natDegree ≤ N} → cod :=
    fun p i => p.1.coeff (i : ℕ)
  have hFin : Finite cod := by
    dsimp [cod]
    infer_instance
  refine @Finite.of_injective {p : F[X] // p.Monic ∧ p.natDegree ≤ N} cod hFin f ?_
  intro p q h
  apply Subtype.ext
  ext i
  by_cases hi : i < N + 1
  · exact congrFun h ⟨i, hi⟩
  · have hge : N < i := by omega
    have hpi : p.1.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt p.2.2 hge)
    have hqi : q.1.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt q.2.2 hge)
    rw [hpi, hqi]

end Commons.FieldTheory.Polynomial