import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Elliptic.WtoW_g_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- Auxiliary bound on the integer coefficients: `|A_{q,j}| + 2|B_{q,j}| ≤ 3^q`.

This is the invariant of the integer recursion `A_{q+1,j} = A_{q,j-1} - 4B_{q,j}`,
`B_{q+1,j} = B_{q,j-1} - A_{q,j}`: the factor `|A| + 2|B|` at level `q+1` is bounded by
`(|A| + 2|B|)|_{q,j-1} + 2 (|A| + 2|B|)|_{q,j} ≤ 3^q + 2·3^q = 3^{q+1}`. -/
theorem WtoW_AB_abs_bound : ∀ q : ℕ, ∀ j : ℕ,
    |WtoW_cA q j| + 2 * |WtoW_cB q j| ≤ (3 : ℝ) ^ q := by
  intro q
  induction q with
  | zero =>
    intro j
    by_cases hj : j = 0
    · subst hj; simp
    · have hA : WtoW_cA 0 j = 0 := by
        simp only [WtoW_cA, WtoW_AB.eq_1, hj, ite_false]; norm_num
      have hB : WtoW_cB 0 j = 0 := by
        simp only [WtoW_cB, WtoW_AB.eq_1, hj, ite_false]; norm_num
      rw [hA, hB]; norm_num
  | succ q ih =>
    intro j
    have hA : |WtoW_cA q j| + 2 * |WtoW_cB q j| ≤ (3 : ℝ) ^ q := ih j
    have hB : |(if j = 0 then (0:ℝ) else WtoW_cA q (j - 1))|
        + 2 * |(if j = 0 then (0:ℝ) else WtoW_cB q (j - 1))| ≤ (3 : ℝ) ^ q := by
      by_cases hj : j = 0
      · subst hj; simp
      · rw [if_neg hj, if_neg hj]; exact ih (j - 1)
    have h1 : |(if j = 0 then (0:ℝ) else WtoW_cA q (j - 1)) - 4 * WtoW_cB q j|
        ≤ |(if j = 0 then (0:ℝ) else WtoW_cA q (j - 1))| + 4 * |WtoW_cB q j| := by
      have h := abs_add_le (if j = 0 then (0:ℝ) else WtoW_cA q (j - 1))
        (-(4 * WtoW_cB q j))
      rw [abs_neg, abs_mul] at h
      simpa [sub_eq_add_neg] using h
    have h2 : |(if j = 0 then (0:ℝ) else WtoW_cB q (j - 1)) - WtoW_cA q j|
        ≤ |(if j = 0 then (0:ℝ) else WtoW_cB q (j - 1))| + |WtoW_cA q j| := by
      have h := abs_add_le (if j = 0 then (0:ℝ) else WtoW_cB q (j - 1))
        (-(WtoW_cA q j))
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    rw [WtoW_cA_succ, WtoW_cB_succ, pow_succ]
    nlinarith [h1, h2, hA, hB, abs_nonneg (WtoW_cA q j), abs_nonneg (WtoW_cB q j)]

theorem WtoW_g_coeff_bound (q j : ℕ) (θ : ℝ) :
    |Work.Elliptic.WtoW_ccoeff q j θ| ≤ 3 * (5 : ℝ) ^ q := by
  have hAB : |WtoW_cA q j| + 2 * |WtoW_cB q j| ≤ (3 : ℝ) ^ q := WtoW_AB_abs_bound q j
  have hX : |WtoW_X θ| ≤ 2 := by
    have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    simp only [WtoW_X, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
  have hstep : |WtoW_cA q j + WtoW_cB q j * WtoW_X θ|
      ≤ |WtoW_cA q j| + 2 * |WtoW_cB q j| := by
    calc |WtoW_cA q j + WtoW_cB q j * WtoW_X θ|
        ≤ |WtoW_cA q j| + |WtoW_cB q j * WtoW_X θ| := abs_add_le _ _
      _ = |WtoW_cA q j| + |WtoW_cB q j| * |WtoW_X θ| := by rw [abs_mul]
      _ ≤ |WtoW_cA q j| + |WtoW_cB q j| * 2 := by
            linarith [mul_le_mul_of_nonneg_left hX (abs_nonneg (WtoW_cB q j))]
      _ = |WtoW_cA q j| + 2 * |WtoW_cB q j| := by ring
  have hfinal : (3 : ℝ) ^ q ≤ 3 * (5 : ℝ) ^ q := by
    have h35 : (3 : ℝ) ^ q ≤ (5 : ℝ) ^ q := by gcongr; norm_num
    have h5 : (0 : ℝ) ≤ 5 ^ q := by positivity
    nlinarith
  calc |WtoW_ccoeff q j θ| = |WtoW_cA q j + WtoW_cB q j * WtoW_X θ| := by
        simp only [WtoW_ccoeff]
    _ ≤ |WtoW_cA q j| + 2 * |WtoW_cB q j| := hstep
    _ ≤ (3 : ℝ) ^ q := hAB
    _ ≤ 3 * (5 : ℝ) ^ q := hfinal

end Work.Elliptic
