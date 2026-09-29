import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17I

open Real

/-- Auxiliary arithmetic. The gap hypothesis, written multiplicatively as `10⁶·|m−n| ≤ n`,
unfolds to `16·((2n+1) − (2m+1)) ≤ 2m+1`: with `g = n − m ≥ 1` it says `10⁶·g ≤ n = m + g`, hence
`(10⁶−1)·g ≤ m`, and `16 ≤ 10⁶−1` gives `16·g ≤ m`, i.e. `32·g ≤ 2m ≤ 2m+1`. -/
theorem gap_le_sixteenth (m n : ℕ) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) :
    16 * ((2 * (n : ℝ) + 1) - (2 * (m : ℝ) + 1)) ≤ 2 * (m : ℝ) + 1 := by
  have hmn : m ≤ n := le_of_lt hlt
  have hg : ((m : ℤ) - n).natAbs = n - m := by
    rw [show ((m : ℤ) - n) = -((n : ℤ) - (m : ℤ)) by ring, Int.natAbs_neg]
    rw [← Nat.cast_sub hmn, Int.natAbs_natCast]
  rw [hg] at hgap
  have h2 : (10 ^ 6 - 1) * (n - m) ≤ m := by omega
  have h3 : 16 * (n - m) ≤ m := by
    have := Nat.mul_le_mul_right (n - m) (by norm_num : 16 ≤ 10 ^ 6 - 1)
    omega
  have h4 : (16 : ℝ) * ((n - m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  have h5 : ((n : ℝ) - (m : ℝ)) = ((n - m : ℕ) : ℝ) := by rw [Nat.cast_sub hmn]
  linarith

/-- Auxiliary numerical inequality. For reals `9/2 ≤ a ≤ b` with `16(b−a) ≤ a` the cusp
`(a+√(a²−1))·(b−√(b²−1))` is at least `8/9`. Both factors are estimated at `a,b`:
`a + √(a²−1) ≥ 2a − 1/2` and `b − √(b²−1) = 1/(b + √(b²−1)) ≥ 1/(2b)`, so the product is at least
`(2a − 1/2)/(2b) ≥ (2a − 1/2)/(17a/8) = (16a − 4)/(17a) ≥ 8/9` (the last step being `8a ≥ 36`). -/
theorem eight_ninths_le_of_gap {a b : ℝ} (ha : 9 / 2 ≤ a) (hab : a ≤ b)
    (hgap : 16 * (b - a) ≤ a) :
    (8 : ℝ) / 9 ≤ (a + Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1)) := by
  have hb1 : (1 : ℝ) < b := by linarith
  have ha2 : (0 : ℝ) ≤ a ^ 2 - 1 := by nlinarith
  have hb2 : (0 : ℝ) ≤ b ^ 2 - 1 := by nlinarith
  -- lower bound for the first factor
  have hX : (2 * a - 1 / 2) ≤ a + Real.sqrt (a ^ 2 - 1) := by
    have h : a - 1 / 2 ≤ Real.sqrt (a ^ 2 - 1) := by
      rw [Real.le_sqrt (by linarith) ha2]
      nlinarith
    linarith
  -- the second factor equals `1/(b + √(b²−1)) ≥ 1/(2b)`
  have hW : 1 / (2 * b) ≤ b - Real.sqrt (b ^ 2 - 1) := by
    have hs : Real.sqrt (b ^ 2 - 1) ≤ b := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hYpos : 0 < b + Real.sqrt (b ^ 2 - 1) := by
      linarith [Real.sqrt_nonneg (b ^ 2 - 1)]
    have hYle : b + Real.sqrt (b ^ 2 - 1) ≤ 2 * b := by linarith
    have hmul : (b - Real.sqrt (b ^ 2 - 1)) * (b + Real.sqrt (b ^ 2 - 1)) = 1 := by
      have h := Real.sq_sqrt hb2
      nlinarith [h]
    have hrec : b - Real.sqrt (b ^ 2 - 1) = 1 / (b + Real.sqrt (b ^ 2 - 1)) := by
      rw [eq_div_iff (ne_of_gt hYpos)]
      linear_combination hmul
    rw [hrec]
    exact one_div_le_one_div_of_le hYpos hYle
  have hble : 4 * b ≤ 17 * a / 4 := by nlinarith [hgap]
  have htarget : (8 : ℝ) / 9 ≤ (2 * a - 1 / 2) * (1 / (2 * b)) := by
    rw [mul_one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * b)]
    nlinarith [hble, ha]
  refine le_trans htarget (mul_le_mul hX hW (by positivity) ?_)
  nlinarith [Real.sqrt_nonneg (a ^ 2 - 1)]

/-- The gap hypothesis `10⁶·|m − n| ≤ n` forces the cusp `x_s = xsOf m n` to satisfy `x_s ≥ 8/9`.
(Used below to see that the disc `ball(x_s, δ)` with `2δ ≤ 1 − x_s` reaches past the radius `5/6`.) -/
theorem xsOf_ge_eight_ninths (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) : (8 : ℝ) / 9 ≤ Work.C17.xsOf m n := by
  have hA := gap_le_sixteenth m n hlt hgap
  have hle : (2 * (m : ℝ) + 1) ≤ 2 * (n : ℝ) + 1 := by
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hlt
    linarith
  have hD : (2 : ℝ) ≤ (2 * (n : ℝ) + 1) - (2 * (m : ℝ) + 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have h2 : (m : ℝ) + 1 ≤ (n : ℝ) := by
        have : m + 1 ≤ n := hlt
        exact_mod_cast this
      linarith
    linarith
  have ha : (9 : ℝ) / 2 ≤ 2 * (m : ℝ) + 1 := by nlinarith [hA, hD]
  have hmain := eight_ninths_le_of_gap ha hle hA
  simpa only [Work.C17.xsOf, Work.C17.xs] using hmain

end Work.C17I
