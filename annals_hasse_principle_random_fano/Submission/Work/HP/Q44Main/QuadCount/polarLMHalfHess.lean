import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polar_basic

namespace Work.HP.Q44Main.QuadCount

open MvPolynomial

/-- The second partial derivative `∂_i ∂_j Q` evaluated at `0` extracts the coefficient of
`X_i X_j` from `Q`, up to the factor `2` on the diagonal.

Concretely, `hess Q i j = Q.coeff (X_i X_j)` for `i ≠ j` and `hess Q i i = 2 * Q.coeff (X_i ^ 2)`;
both are subsumed by the single formula `hess Q i j = (if i = j then 2 else 1) * Q.coeff (X_i X_j)`.

This holds for an *arbitrary* polynomial `Q` (no homogeneity is needed): the second derivative
of a monomial `X^α` kills every multi-index `α` of total degree `≠ 2`. -/
lemma hess_coeff (Q : MvPolynomial (Fin 5) ℚ) (i j : Fin 5) :
    Work.HP.MDEstimates.hess Q i j
      = (if i = j then (2:ℚ) else 1) * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) := by
  unfold Work.HP.MDEstimates.hess
  rw [coeff_pderiv, coeff_pderiv]
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one]
  rw [Finsupp.single_apply]
  split_ifs with h <;> ring

/-- The coefficient matrix of the polar form is half the Hessian: `polarLM Q v i` equals
`(1/2) * ∑_j hess Q i j * v j`.  The point of the identity is the diagonal factor `2`
(`polarLM Q v i` averages the off-diagonal contribution with *twice* the diagonal one). -/
theorem polarLMHalfHess (Q : MvPolynomial (Fin 5) ℚ) (v : Fin 5 → ℚ) (i : Fin 5) :
    (Work.HP.MDEstimates.polarLM Q v) i
      = (1/2) * ∑ j : Fin 5, Work.HP.MDEstimates.hess Q i j * v j := by
  have hLHS : (Work.HP.MDEstimates.polarLM Q v) i
      = ((∑ j : Fin 5, Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j)
          + Q.coeff (Finsupp.single i 1 + Finsupp.single i 1) * v i) / 2 := by
    simp only [Work.HP.MDEstimates.polarLM, LinearMap.coe_mk, AddHom.coe_mk]
  have hsum2 : ∑ j : Fin 5, Work.HP.MDEstimates.hess Q i j * v j
      = (∑ j : Fin 5, Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j)
        + Q.coeff (Finsupp.single i 1 + Finsupp.single i 1) * v i := by
    have hstep : ∀ j : Fin 5,
        Work.HP.MDEstimates.hess Q i j * v j
          = Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j
            + (if i = j then (1:ℚ) else 0)
              * (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j) := by
      intro j
      rw [hess_coeff Q i j]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : ¬ (i = b) := fun h => hb h.symm
      simp [this]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hLHS, hsum2]
  ring

end Work.HP.Q44Main.QuadCount
