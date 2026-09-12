import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

theorem X2_mul_left_cancel {n : ℕ} [Nonempty (Fin n)] {a b : MvPolynomial (Fin n) ℝ}
    (h : (∑ j : Fin n, (MvPolynomial.X j)^2) * a = (∑ j : Fin n, (MvPolynomial.X j)^2) * b) :
    a = b := by
  classical
  -- The sum of squares is a nonzero polynomial (its coefficient at the
  -- monomial `X j₀ ^ 2` is `1`), and `MvPolynomial (Fin n) ℝ` is an integral
  -- domain, so multiplication by it is left-cancellative.
  obtain ⟨j₀⟩ := ‹Nonempty (Fin n)›
  let m : Fin n →₀ ℕ := Finsupp.single j₀ 2
  have hS : (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)^2) ≠ 0 := by
    have hcoef :
        MvPolynomial.coeff m (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)^2) =
          (1 : ℝ) := by
      rw [MvPolynomial.coeff_sum Finset.univ (fun j : Fin n => (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)^2) m]
      rw [Finset.sum_eq_single j₀]
      · simp [m, MvPolynomial.coeff_X_pow]
      · intro j _hj hne
        have hne2 : Finsupp.single j 2 ≠ Finsupp.single j₀ 2 := by
          intro hEq
          exact hne ((Finsupp.single_left_inj (by norm_num : (2 : ℕ) ≠ 0)).mp hEq)
        simp [m, MvPolynomial.coeff_X_pow, hne2]
      · intro hj₀
        simp at hj₀
    intro hS
    have : (0 : ℝ) = 1 := by
      rw [← hcoef, hS]
      simp
    norm_num at this
  exact mul_left_cancel₀ hS h

end Commons.Algebra.MvPolynomial