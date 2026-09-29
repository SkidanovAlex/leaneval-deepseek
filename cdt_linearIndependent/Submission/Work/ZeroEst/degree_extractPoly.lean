import Mathlib
import Submission.Work.ZeroEst.defs

namespace Work.ZeroEst

theorem degree_extractPoly {d D : ℕ} (P : MvPolynomial (Fin d) ℚ) (g : Fin d → PowerSeries ℚ)
    (n : Fin d →₀ ℕ) (j : Fin d) (hD : P.degreeOf j < D) :
    (∑ c ∈ P.support,
        if ∀ s, s ≠ j → c s ≤ n s then
          Polynomial.monomial (c j)
            (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
        else 0 : Polynomial ℚ).degree < (D : WithBot ℕ) := by
  classical
  have key : ∀ c ∈ P.support,
      (if ∀ s, s ≠ j → c s ≤ n s then
        Polynomial.monomial (c j)
          (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
      else 0 : Polynomial ℚ).degree ≤ (P.degreeOf j : WithBot ℕ) := by
    intro c hc
    by_cases h : ∀ s, s ≠ j → c s ≤ n s
    · rw [if_pos h]
      exact (Polynomial.degree_monomial_le (c j) _).trans
        (by exact_mod_cast MvPolynomial.le_degreeOf_of_mem_support j hc)
    · rw [if_neg h]; exact bot_le
  exact ((Polynomial.degree_sum_le P.support _).trans (Finset.sup_le key)).trans_lt
    (by exact_mod_cast hD)

end Work.ZeroEst
