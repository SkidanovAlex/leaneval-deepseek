import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Inequalities

/-- A pure real-arithmetic inequality used to absorb a Lipschitz oscillation bound into an
`o(r^2)` average bound. -/
theorem pow_five_div_bound {A ε r K u c : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hr : 0 < r) (hK : 0 < K)
    (hc : c ≤ ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2))
    (hK_le : K ≤ 2 * A * r) (hu : ε * r ^ 2 ≤ u) :
    c * r ^ 2 ≤ u ^ 5 / (32 * K ^ 4 * r ^ 4) := by
  have hA2nn : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have hA1pos : (0 : ℝ) < A ^ 2 + 1 := by nlinarith [hA]
  have hnd : (0 : ℝ) < 512 * (A ^ 2 + 1) ^ 2 := by positivity
  have hD : (0 : ℝ) < 32 * K ^ 4 * r ^ 4 := by positivity
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr 2
  have hε5 : (0 : ℝ) < ε ^ 5 := pow_pos hε 5
  -- Step 1: bound `K ^ 4` by `16 * (A^2+1)^2 * r^4`.
  have hK4 : K ^ 4 ≤ 16 * (A ^ 2 + 1) ^ 2 * r ^ 4 := by
    have h1 : K ^ 4 ≤ (2 * A * r) ^ 4 := pow_le_pow_left₀ (le_of_lt hK) hK_le 4
    have h2 : (2 * A * r) ^ 4 = 16 * A ^ 4 * r ^ 4 := by ring
    have h3 : A ^ 4 ≤ (A ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg A]
    have hr4 : (0 : ℝ) ≤ r ^ 4 := by positivity
    rw [h2] at h1
    nlinarith [h1, h3, hr4]
  -- Step 2: bound `u ^ 5` from below by `ε ^ 5 * r ^ 10`.
  have hu5 : ε ^ 5 * r ^ 10 ≤ u ^ 5 := by
    have h1 : (ε * r ^ 2) ^ 5 ≤ u ^ 5 :=
      pow_le_pow_left₀ (le_of_lt (mul_pos hε hr2)) hu 5
    have h2 : (ε * r ^ 2) ^ 5 = ε ^ 5 * r ^ 10 := by ring
    rwa [h2] at h1
  -- Step 3: multiply `hc` by the nonnegative factors `r ^ 2` and `32 * K ^ 4 * r ^ 4`.
  have hcr : c * r ^ 2 * (32 * K ^ 4 * r ^ 4)
      ≤ (ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2)) * r ^ 2 * (32 * K ^ 4 * r ^ 4) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (le_of_lt hr2)) (le_of_lt hD)
  -- Step 4: absorb the denominator using the bound on `K ^ 4`.
  have hmid : (ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2)) * r ^ 2 * (32 * K ^ 4 * r ^ 4)
      ≤ ε ^ 5 * r ^ 10 := by
    have heq : (ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2)) * r ^ 2 * (32 * K ^ 4 * r ^ 4)
        = (ε ^ 5 * r ^ 2 * (32 * K ^ 4 * r ^ 4)) / (512 * (A ^ 2 + 1) ^ 2) := by ring
    rw [heq, div_le_iff₀ hnd]
    have hfac : (0 : ℝ) ≤ 32 * ε ^ 5 * r ^ 6 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hK4 hfac
    nlinarith [hstep]
  rw [le_div_iff₀ hD]
  exact le_trans hcr (le_trans hmid hu5)

end Commons.Analysis.Inequalities