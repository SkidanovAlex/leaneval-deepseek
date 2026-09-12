import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral

open Polynomial

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

theorem minpoly_leading_coeff_eq_one (α : ℂ) (hα : IsAlgebraic ℚ α) :
    (minpoly ℚ α).coeff (minpoly ℚ α).natDegree = 1 := by
  rw [Polynomial.coeff_natDegree]
  exact (minpoly.monic (IsAlgebraic.isIntegral hα)).leadingCoeff

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree