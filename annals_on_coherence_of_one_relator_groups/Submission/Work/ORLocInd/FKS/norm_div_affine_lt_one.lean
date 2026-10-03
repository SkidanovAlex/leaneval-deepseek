import Mathlib

namespace Work.ORLocInd.FKS

/-- A complex number `w` with nonzero imaginary part and `‖w‖ ≥ 1`, and an integer `N` with
`|N| ≥ 2`, satisfy `‖w / (N*w + 1)‖ < 1`: indeed
`‖N*w + 1‖^2 - ‖w‖^2 = (N^2 - 1)‖w‖^2 + 2*N*Re w + 1 > (N^2 - 1)‖w‖^2 - 2|N|‖w‖ + 1 ≥ 0`, the
strict inequality coming from `|Re w| < ‖w‖` (as `w.im ≠ 0`), and the last one from
`|N| ≥ 2` and `‖w‖ ≥ 1`. -/
theorem norm_div_affine_lt_one {w : ℂ} {N : ℤ} (him : w.im ≠ 0) (h1 : 1 ≤ ‖w‖) (hN : 2 ≤ |N|) :
    ‖w / ((N : ℂ) * w + 1)‖ < 1 := by
  set n : ℝ := (N : ℝ) with hn
  set x : ℝ := w.re with hx
  set y : ℝ := w.im with hy
  set r : ℝ := ‖w‖ with hr
  have hnorm2 : ‖w‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hx, ← hy]; ring
  have hDnorm : ‖((N : ℂ) * w + 1)‖ ^ 2 = (n * x + 1) ^ 2 + (n * y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1re : ((N : ℂ) * w + 1).re = n * x + 1 := by
      rw [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.one_re, ← hn, ← hx, ← hy]; ring
    have h1im : ((N : ℂ) * w + 1).im = n * y := by
      rw [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.one_im, ← hn, ← hx, ← hy]; ring
    rw [h1re, h1im]; ring
  have h1' : 1 ≤ r := by rw [hr]; exact h1
  have hN' : (2 : ℝ) ≤ |n| := by
    rw [hn, ← Int.cast_abs]; exact_mod_cast hN
  have hxabs : |x| < r := by
    rw [hx, hr]; exact Complex.abs_re_lt_norm.mpr him
  have hxa := abs_lt.mp hxabs
  -- The key real inequality: `(n²-1)r² + 2nx + 1 > 0`.
  have hgoal_pos : (n ^ 2 - 1) * r ^ 2 + 2 * n * x + 1 > 0 := by
    by_cases hn0 : 0 ≤ n
    · have hnn : (|n| : ℝ) = n := abs_of_nonneg hn0
      have h2 : 2 ≤ n := by rw [← hnn]; exact hN'
      have hs : 0 ≤ n * r - 1 - r := by nlinarith [h2, h1']
      have ht : 0 ≤ n * r - 1 + r := by nlinarith [h2, h1']
      have hbase : n ^ 2 * r ^ 2 - 2 * n * r + 1 - r ^ 2 ≥ 0 := by
        nlinarith [mul_nonneg hs ht]
      have hg1 : 2 * n * x > -2 * n * r := by nlinarith [hxa.1, h2]
      nlinarith [hbase, hg1]
    · have hn0' : n < 0 := not_le.mp hn0
      have hnn : (|n| : ℝ) = -n := abs_of_neg hn0'
      have h2 : 2 ≤ -n := by rw [← hnn]; exact hN'
      have hs : 0 ≤ (-n) * r - 1 - r := by nlinarith [h2, h1']
      have ht : 0 ≤ (-n) * r - 1 + r := by nlinarith [h2, h1']
      have hbase : (-n) ^ 2 * r ^ 2 - 2 * (-n) * r + 1 - r ^ 2 ≥ 0 := by
        nlinarith [mul_nonneg hs ht]
      have hg1 : 2 * n * x > -2 * (-n) * r := by nlinarith [hxa.2, h2]
      nlinarith [hbase, hg1]
  have hdiff : ‖((N : ℂ) * w + 1)‖ ^ 2 - ‖w‖ ^ 2 = (n ^ 2 - 1) * r ^ 2 + 2 * n * x + 1 := by
    rw [hDnorm, hnorm2]; ring
  have hsqgt : ‖w‖ ^ 2 < ‖((N : ℂ) * w + 1)‖ ^ 2 := by
    have : 0 < ‖((N : ℂ) * w + 1)‖ ^ 2 - ‖w‖ ^ 2 := by rw [hdiff]; exact hgoal_pos
    linarith
  have hlt : ‖w‖ < ‖((N : ℂ) * w + 1)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg (((N : ℂ) * w + 1))) hsqgt
  have hzpos : 0 < ‖((N : ℂ) * w + 1)‖ := lt_of_le_of_lt (norm_nonneg w) hlt
  rw [norm_div, div_lt_one hzpos]
  exact hlt

end Work.ORLocInd.FKS
