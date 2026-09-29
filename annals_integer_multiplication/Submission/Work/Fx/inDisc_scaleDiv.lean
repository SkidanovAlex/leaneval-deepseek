import Mathlib
import Submission.Work.Fx.scaleCommon

namespace Work.Fx

/-- **Truncating division shrinks the modulus.** For a positive divisor `b : ℕ`,
`|trunc(A/b)| · b ≤ |A|` (real form of `natAbs_tdiv_mul_le`). -/
theorem abs_tdiv_mul_le (A : ℤ) {b : ℕ} (hb : 0 < b) :
    |(((A.tdiv (b : ℤ) : ℤ)) : ℝ)| * (b : ℝ) ≤ |(A : ℝ)| := by
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have h := natAbs_tdiv_mul_le A hbZ
  rw [Int.natAbs_natCast] at h
  have hR : ((A.tdiv (b : ℤ)).natAbs : ℝ) * (b : ℝ) ≤ (A.natAbs : ℝ) := by exact_mod_cast h
  have e1 : |(((A.tdiv (b : ℤ) : ℤ)) : ℝ)| = ((A.tdiv (b : ℤ)).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  have e2 : |(A : ℝ)| = (A.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  rw [e1, e2]
  exact hR

/-- **Scaling down into the disc.** If `b ≥ 2^p` and `(X, Y)` lies strictly inside the circle of
radius `b`, then the point `(2^p X / b, 2^p Y / b)` truncated towards zero componentwise lies in the
fixed-point disc `x² + y² ≤ 4^p`.

Indeed, `|trunc(2^p X / b)| · b ≤ 2^p |X|`, so squaring and adding the two coordinates,
`(x² + y²) b² ≤ 4^p (X² + Y²) < 4^p b²`, and division by `b² > 0` gives `x² + y² < 4^p`. -/
theorem inDisc_scaleDiv {p : ℕ} {X Y : ℤ} {b : ℕ}
    (hb1 : 2 ^ p ≤ b)
    (hb2 : (b : ℝ) ^ 2 > (X : ℝ) ^ 2 + (Y : ℝ) ^ 2) :
    HvdH.inDisc p (Int.tdiv ((2 : ℤ) ^ p * X) b, Int.tdiv ((2 : ℤ) ^ p * Y) b) := by
  have hbpos : 0 < b := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) p) hb1
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hqR : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (by norm_num) p
  have hA := abs_tdiv_mul_le ((2 : ℤ) ^ p * X) hbpos
  have hB := abs_tdiv_mul_le ((2 : ℤ) ^ p * Y) hbpos
  have hA2 : ((((2 : ℤ) ^ p * X).tdiv (b : ℤ) : ℤ) : ℝ) ^ 2 * (b : ℝ) ^ 2
      ≤ (((2 : ℤ) ^ p * X : ℤ) : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (le_of_lt hbR)) hA 2
    rwa [mul_pow, sq_abs, sq_abs] at h
  have hB2 : ((((2 : ℤ) ^ p * Y).tdiv (b : ℤ) : ℤ) : ℝ) ^ 2 * (b : ℝ) ^ 2
      ≤ (((2 : ℤ) ^ p * Y : ℤ) : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (le_of_lt hbR)) hB 2
    rwa [mul_pow, sq_abs, sq_abs] at h
  push_cast at hA2 hB2
  have hpow : (4 : ℝ) ^ p = ((2 : ℝ) ^ p) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have keyR : ((((2 : ℤ) ^ p * X).tdiv (b : ℤ) : ℤ) : ℝ) ^ 2
      + ((((2 : ℤ) ^ p * Y).tdiv (b : ℤ) : ℤ) : ℝ) ^ 2 < (4 : ℝ) ^ p := by
    rw [hpow]
    have hlt : ((2 : ℝ) ^ p) ^ 2 * ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) < ((2 : ℝ) ^ p) ^ 2 * (b : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_left hb2 (pow_pos hqR 2)
    nlinarith [hA2, hB2, hlt, pow_pos hbR 2, hqR]
  rw [HvdH.inDisc]
  exact_mod_cast (le_of_lt keyR)

end Work.Fx
