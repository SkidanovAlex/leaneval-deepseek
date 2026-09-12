import Mathlib.RingTheory.Polynomial.Pochhammer
import Submission.Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq

namespace Commons.Combinatorics.MvPolynomial

theorem exists_polynomial_ncard_degree {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : Polynomial ℚ, ∀ m : ℕ, (Set.ncard {c : Fin n →₀ ℕ | c.degree = m} : ℚ) = Q.eval (m : ℚ) := by
  refine ⟨Polynomial.C (((n - 1).factorial : ℚ))⁻¹ *
    (ascPochhammer ℚ (n - 1)).comp (Polynomial.X + 1), ?_⟩
  intro m
  have hcount : Set.ncard {c : Fin n →₀ ℕ | c.degree = m} = (n + m - 1).choose m := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {c : Fin n →₀ ℕ // c.degree = m} = (n + m - 1).choose m
    rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq (Fin n) m, Fintype.card_fin]
  rw [hcount, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have heval : (ascPochhammer ℚ (n - 1)).eval ((m : ℚ) + 1) =
      (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) := by
    rw [show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; ring]
    rw [ascPochhammer_nat_eq_natCast_ascFactorial]
    rw [← Nat.add_descFactorial_eq_ascFactorial' (m + 1) (n - 1)]
    rw [show (m + 1) + (n - 1) - 1 = m + n - 1 by omega]
  rw [heval]
  have hchoose : (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) =
      ((n - 1).factorial : ℚ) * ((m + n - 1).choose (n - 1) : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hchoose]
  have hsym : (m + n - 1).choose (n - 1) = (n + m - 1).choose m := by
    rw [Nat.add_comm n m]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hsym]
  have hne : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel_left₀ hne]

end Commons.Combinatorics.MvPolynomial