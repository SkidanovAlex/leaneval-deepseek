import Mathlib
import Submission.Commons.Analysis.Sigma2.sharp_minEigen_four

namespace Commons.Analysis.Sigma2

/-! Lower bound `f_i > 1/sigma_1` for every linearized eigenvalue `f_i = sigma_1 - lambda_i` in dimension 4 with sigma_2 = 1 and sigma_1 > 0 (Corollary 1.3 of Shankar--Yuan, first inequality, valid for all i).  Proof: `f_i * (sigma_1 + lam i) = sigma_1^2 - lam i^2 = 2 + sum_{j ≠ i} lam j^2 > 2`, and `sigma_1 + lam i < 2 * sigma_1` because `lam i < sigma_1` (use the sharp bound), hence `f_i > 1/sigma_1`. -/
open scoped BigOperators

/-- A sum of three squares plus the three pairwise products is positive unless all three
variables vanish: indeed it equals `(1/2) * ((x+y+z)^2 + x^2 + y^2 + z^2)`. -/
private lemma triple_sq_sum_pos (x y z : ℝ) (hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z := by
  have hid : 2 * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z) =
      (x + y + z) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by ring
  rcases hxyz with hx | hy | hz
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    nlinarith [hid, hx2, sq_nonneg (x + y + z), sq_nonneg y, sq_nonneg z]
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    nlinarith [hid, hy2, sq_nonneg (x + y + z), sq_nonneg x, sq_nonneg z]
  · have hz2 : 0 < z ^ 2 := sq_pos_of_ne_zero hz
    nlinarith [hid, hz2, sq_nonneg (x + y + z), sq_nonneg x, sq_nonneg y]

theorem linearized_lower_inverse_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    ∀ i : Fin 4, 1 / (∑ j : Fin 4, lam j) < (∑ j : Fin 4, lam j) - lam i := by
  -- sigma_2 = 1, expanded over the six unordered pairs.
  have hσ2e : lam 0 * lam 1 + lam 0 * lam 2 + lam 0 * lam 3 +
      lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3 = 1 := by
    simpa [pairSumFin4] using hσ2
  -- sigma_1 > 0, expanded.
  have hs : (∑ j : Fin 4, lam j) = lam 0 + lam 1 + lam 2 + lam 3 := sumFin4 lam
  rw [hs] at hσ1
  intro i
  fin_cases i
  · -- i = 0: f_0 = lam 1 + lam 2 + lam 3
    rw [hs]
    simp
    rw [← one_div]
    have hR : 0 < (lam 1) ^ 2 + (lam 2) ^ 2 + (lam 3) ^ 2 +
        lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3 := by
      apply triple_sq_sum_pos (lam 1) (lam 2) (lam 3)
      by_contra hnt
      push_neg at hnt
      rcases hnt with ⟨h1, h2, h3⟩
      nlinarith [hσ2e]
    have hmul : 1 < (lam 0 + lam 1 + lam 2 + lam 3 - lam 0) *
        (lam 0 + lam 1 + lam 2 + lam 3) := by
      nlinarith [hσ2e, hR]
    exact (div_lt_iff₀ hσ1).2 hmul
  · -- i = 1: f_1 = lam 0 + lam 2 + lam 3
    rw [hs]
    simp
    rw [← one_div]
    have hR : 0 < (lam 0) ^ 2 + (lam 2) ^ 2 + (lam 3) ^ 2 +
        lam 0 * lam 2 + lam 0 * lam 3 + lam 2 * lam 3 := by
      apply triple_sq_sum_pos (lam 0) (lam 2) (lam 3)
      by_contra hnt
      push_neg at hnt
      rcases hnt with ⟨h0, h2, h3⟩
      nlinarith [hσ2e]
    have hmul : 1 < (lam 0 + lam 1 + lam 2 + lam 3 - lam 1) *
        (lam 0 + lam 1 + lam 2 + lam 3) := by
      nlinarith [hσ2e, hR]
    exact (div_lt_iff₀ hσ1).2 hmul
  · -- i = 2: f_2 = lam 0 + lam 1 + lam 3
    rw [hs]
    simp
    rw [← one_div]
    have hR : 0 < (lam 0) ^ 2 + (lam 1) ^ 2 + (lam 3) ^ 2 +
        lam 0 * lam 1 + lam 0 * lam 3 + lam 1 * lam 3 := by
      apply triple_sq_sum_pos (lam 0) (lam 1) (lam 3)
      by_contra hnt
      push_neg at hnt
      rcases hnt with ⟨h0, h1, h3⟩
      nlinarith [hσ2e]
    have hmul : 1 < (lam 0 + lam 1 + lam 2 + lam 3 - lam 2) *
        (lam 0 + lam 1 + lam 2 + lam 3) := by
      nlinarith [hσ2e, hR]
    exact (div_lt_iff₀ hσ1).2 hmul
  · -- i = 3: f_3 = lam 0 + lam 1 + lam 2
    rw [hs]
    simp
    rw [← one_div]
    have hR : 0 < (lam 0) ^ 2 + (lam 1) ^ 2 + (lam 2) ^ 2 +
        lam 0 * lam 1 + lam 0 * lam 2 + lam 1 * lam 2 := by
      apply triple_sq_sum_pos (lam 0) (lam 1) (lam 2)
      by_contra hnt
      push_neg at hnt
      rcases hnt with ⟨h0, h1, h2⟩
      nlinarith [hσ2e]
    have hmul : 1 < (lam 0 + lam 1 + lam 2) *
        (lam 0 + lam 1 + lam 2 + lam 3) := by
      nlinarith [hσ2e, hR]
    exact (div_lt_iff₀ hσ1).2 hmul

end Commons.Analysis.Sigma2
