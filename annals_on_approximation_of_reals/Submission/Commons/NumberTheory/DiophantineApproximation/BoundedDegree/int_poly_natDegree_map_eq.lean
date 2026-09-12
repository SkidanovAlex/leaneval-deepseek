import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

theorem int_poly_natDegree_map_eq (P : Polynomial ℤ) :
    (P.map (Int.castRingHom ℝ)).natDegree = P.natDegree := by
  by_cases hP : P = 0
  · subst hP
    simp
  · have hle : (P.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree := by
      exact Polynomial.natDegree_map_le
    have hc : P.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact (Polynomial.leadingCoeff_eq_zero.not.mpr hP)
    have hcmap : (P.map (Int.castRingHom ℝ)).coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_map]
      intro hz
      exact hc ((map_eq_zero_iff (Int.castRingHom ℝ) (by exact Int.cast_injective)).mp hz)
    have hge : P.natDegree ≤ (P.map (Int.castRingHom ℝ)).natDegree := by
      apply Nat.le_of_not_gt (a := (P.map (Int.castRingHom ℝ)).natDegree) (b := P.natDegree)
      intro hlt
      exact hcmap (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
    exact le_antisymm hle hge

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree