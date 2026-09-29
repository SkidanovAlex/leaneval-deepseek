import Mathlib
import Submission.Work.ANum3.ZcertDefs

/-!
# A lower bound for the lune radicand `luneR (36/5)`

Write `p z = (1 + c²)² (1 + z)² - 16 c² z` for the radicand `luneR c z` of the lune map, and put
`A = (1 + c²)²`, `m = 2A - 16c²`.  On the real and imaginary parts of `z` one has the exact
identity

`‖p z‖² = (2 A · (Re z) + m (1 + ‖z‖²)/2)² + (A² - m²/4) (1 - ‖z‖²)²`,

and the constant `A² - m²/4 = 16 c² (c² - 1)² = (4 c (c² - 1))²` is *positive*.  Hence
`‖luneR c z‖ ≥ 4 c (c² - 1) · (1 - ‖z‖²)` for `‖z‖ ≤ 1` — the minimum modulus of `luneR c` on the
closed unit disc, the zeros of `luneR c` lying on `|z| = 1` (at the cusps of the lune).

For the contour constant `c = 36/5` we have `4 c (c² - 1) = 183024/125 = 1464.192 > 1400`, so the
requested bound holds with the stated slack.
-/

namespace Work.ANum3

/-- The exact "minimum modulus" identity for the quadratic `z ↦ A (1+z)² - B z`: its squared
modulus splits, with a square plus a positive multiple of `(1 - ‖z‖²)²`. -/
private lemma luneR_sq_identity (A B : ℝ) (z : ℂ) :
    ‖(A : ℂ) * (1 + z) ^ 2 - (B : ℂ) * z‖ ^ 2
      = (2 * A * z.re + (2 * A - B) * (1 + ‖z‖ ^ 2) / 2) ^ 2
        + (A ^ 2 - (2 * A - B) ^ 2 / 4) * (1 - ‖z‖ ^ 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, pow_two]
  ring

/-- `A² - m²/4 ≥ 1400²` for `A = (1 + (36/5)²)²`, `m = 2A - 16·(36/5)²`; indeed the left side is
`(4·(36/5)·((36/5)² - 1))² = (183024/125)² = 1464.192²`. -/
private lemma luneR_const_lower :
    (1400 : ℝ) ^ 2 ≤
      ((1 + (36 / 5) ^ 2) ^ 2) ^ 2 - (2 * (1 + (36 / 5) ^ 2) ^ 2 - 16 * (36 / 5) ^ 2) ^ 2 / 4 := by
  norm_num

theorem luneR_abs_lower (z : ℂ) :
    1400 * (1 - ‖z‖ ^ 2) ≤ ‖Work.APsi.luneR (36 / 5) z‖ := by
  set A : ℝ := (1 + (36 / 5) ^ 2) ^ 2 with hA
  set B : ℝ := 16 * (36 / 5) ^ 2 with hB
  have hdeg : Work.APsi.luneR (36 / 5) z = (A : ℂ) * (1 + z) ^ 2 - (B : ℂ) * z := by
    simp only [Work.APsi.luneR, hA, hB]
    push_cast
    ring
  have hid : ‖Work.APsi.luneR (36 / 5) z‖ ^ 2
      = (2 * A * z.re + (2 * A - B) * (1 + ‖z‖ ^ 2) / 2) ^ 2
        + (A ^ 2 - (2 * A - B) ^ 2 / 4) * (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [hdeg]
    exact luneR_sq_identity A B z
  have hα : (1400 : ℝ) ^ 2 ≤ A ^ 2 - (2 * A - B) ^ 2 / 4 := by
    rw [hA, hB]
    exact luneR_const_lower
  by_cases hσ : 0 ≤ 1 - ‖z‖ ^ 2
  · have hkey : (1400 * (1 - ‖z‖ ^ 2)) ^ 2 ≤ ‖Work.APsi.luneR (36 / 5) z‖ ^ 2 := by
      rw [hid]
      have h2 : (1400 * (1 - ‖z‖ ^ 2)) ^ 2 = 1400 ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 := by ring
      rw [h2]
      have h3 : 1400 ^ 2 * (1 - ‖z‖ ^ 2) ^ 2
          ≤ (A ^ 2 - (2 * A - B) ^ 2 / 4) * (1 - ‖z‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hα (sq_nonneg _)
      nlinarith [h3, sq_nonneg (2 * A * z.re + (2 * A - B) * (1 + ‖z‖ ^ 2) / 2)]
    have h4 : |1400 * (1 - ‖z‖ ^ 2)| ≤ |‖Work.APsi.luneR (36 / 5) z‖| := sq_le_sq.mp hkey
    rwa [abs_of_nonneg (mul_nonneg (by norm_num) hσ), abs_of_nonneg (norm_nonneg _)] at h4
  · have h5 : 1400 * (1 - ‖z‖ ^ 2) < 0 :=
      mul_neg_of_pos_of_neg (by norm_num) (not_le.mp hσ)
    linarith [norm_nonneg (Work.APsi.luneR (36 / 5) z)]

end Work.ANum3
