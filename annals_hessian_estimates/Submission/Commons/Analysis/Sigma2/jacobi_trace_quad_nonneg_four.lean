import Mathlib
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.linearized_upper_four
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two

namespace Commons.Analysis.Sigma2

/-! The Jacobi trace estimate needed in the proof of the Hessian estimate for the
sigma-2 equation in dimension four (Shankar--Yuan).  With `lam` the decreasingly
sorted eigenvalue tuple of `D^2 u` (so `sigma_2 = 1`, `sigma_1 = S > 0`) and
`f_i = S - lam_i > 0` the eigenvalue of the linearized operator at entry `i`,
for every `0 ≤ δ ≤ 2` the quantity
`3 - δ * f / S + (2 * f^2 + 6 * (1 + δ * f / S)) / (3 * S^2 - 2)`
is nonnegative.  It splits into two individually nonnegative terms:
`3 - δ * f / S ≥ 0` uses `f ≤ (3/2) S` and `δ ≤ 2`; the fraction is nonnegative
because `3 S^2 - 2 ≥ 4 > 0` (from `S^2 ≥ 2`) and the numerator is `> 0`
(since `f > 0` and `δ ≥ 0`). -/
open scoped BigOperators in
theorem jacobi_trace_quad_nonneg_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (i : Fin 4) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let f : ℝ := S - lam i
    0 ≤ (3 - δ * f / S) + (2 * f ^ 2 + 6 * (1 + δ * f / S)) / (3 * S ^ 2 - 2) := by
  intro S f
  -- `S = sigma_1 > 0`, and `f = S - lam i > 0` (positivity of the linearized operator).
  have hSpos : 0 < S := by
    simpa [S] using hσ1
  have hfpos : 0 < f := by
    have h := linearized_pos_four lam hmono hσ2 hσ1 i
    simpa [S, f] using h
  -- `f ≤ (3/2) S` (upper bound for the eigenvalues of the linearized operator).
  have hfupper : f ≤ (3 / 2 : ℝ) * S := by
    have h := linearized_upper_four lam hmono hσ2 hσ1 i
    simpa [S, f] using h
  -- Denominator: `3 S^2 - 2 ≥ 4 > 0` from `2 ≤ S^2`.
  have hSsq : 2 ≤ S ^ 2 := by
    have h := sigma1_sq_ge_two lam hσ2
    simpa [S] using h
  have hdenpos : 0 < 3 * S ^ 2 - 2 := by
    nlinarith
  -- First term: `3 - δ * f / S ≥ 0` since `δ ≤ 2` and `f ≤ (3/2) S`.
  have hδf : δ * f ≤ 2 * f := mul_le_mul_of_nonneg_right hδ2 (le_of_lt hfpos)
  have hf2 : 2 * f ≤ 3 * S := by
    nlinarith [hfupper]
  have hδf3 : δ * f ≤ 3 * S := le_trans hδf hf2
  have hratio : δ * f / S ≤ 3 := (div_le_iff₀ hSpos).mpr hδf3
  have hterm1 : 0 ≤ 3 - δ * f / S := by
    linarith
  -- Second term: numerator nonnegative, denominator positive.
  have hδfs : 0 ≤ δ * f / S := by
    exact div_nonneg (mul_nonneg hδ0 (le_of_lt hfpos)) (le_of_lt hSpos)
  have hnum : 0 ≤ 2 * f ^ 2 + 6 * (1 + δ * f / S) := by
    have h1 : 0 ≤ 1 + δ * f / S := by linarith
    have h1' : 0 ≤ 6 * (1 + δ * f / S) := mul_nonneg (by norm_num) h1
    have h2 : 0 ≤ 2 * f ^ 2 := mul_nonneg (by norm_num) (sq_nonneg f)
    linarith
  have hfrac : 0 ≤ (2 * f ^ 2 + 6 * (1 + δ * f / S)) / (3 * S ^ 2 - 2) := by
    exact div_nonneg hnum (le_of_lt hdenpos)
  exact add_nonneg hterm1 hfrac

end Commons.Analysis.Sigma2
