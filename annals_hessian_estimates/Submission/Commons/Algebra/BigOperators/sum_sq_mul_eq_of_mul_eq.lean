import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.unusedVariables false

namespace Commons.Algebra.BigOperators

/-- Linearity of a finite sum of a three-term affine combination. -/
lemma sum_three_terms {ι : Type*} [Fintype ι] (u v w : ι → ℝ) (a b c : ℝ) :
    (∑ i, (a * u i - b * v i + c * w i))
      = a * (∑ i, u i) - b * (∑ i, v i) + c * (∑ i, w i) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

theorem sum_sq_mul_eq_of_mul_eq {n : ℕ} (f c lam xc : Fin n → ℝ) {q Z hh : ℝ} (hZ : Z ≠ 0)
    (hlam : ∀ i, lam i * c i = q * (2 * xc i / Z - hh * c i)) :
    (∑ i, f i * (c i * lam i) ^ 2)
      = q ^ 2 * (4 * (∑ i, f i * (xc i) ^ 2) / Z ^ 2
          - 4 * hh * (∑ i, f i * c i * xc i) / Z
          + hh ^ 2 * (∑ i, f i * (c i) ^ 2)) := by
  -- Step 1: replace `c i * lam i` using the hypothesis.
  have hstep1 : (∑ i, f i * (c i * lam i) ^ 2)
      = ∑ i, f i * (q * (2 * xc i / Z - hh * c i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show c i * lam i = q * (2 * xc i / Z - hh * c i) from by
      rw [mul_comm]; exact hlam i]
  rw [hstep1]
  -- Step 2: factor out `q ^ 2` from each term.
  have hstep2 : (∑ i, f i * (q * (2 * xc i / Z - hh * c i)) ^ 2)
      = q ^ 2 * ∑ i, f i * (2 * xc i / Z - hh * c i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hstep2]
  congr 1
  -- Step 3: expand the square and use linearity of the sum.
  rw [show (∑ i, f i * (2 * xc i / Z - hh * c i) ^ 2)
        = ∑ i, ((4 / Z ^ 2) * (f i * (xc i) ^ 2) - (4 * hh / Z) * (f i * c i * xc i)
            + hh ^ 2 * (f i * (c i) ^ 2)) from by
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [sum_three_terms]
  ring

end Commons.Algebra.BigOperators