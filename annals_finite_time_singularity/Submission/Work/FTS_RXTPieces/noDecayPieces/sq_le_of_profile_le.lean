import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

theorem sq_le_of_profile_le {v : ℝ → ℝ} {z K : ℝ} (hz : 0 < z) (hK : 0 ≤ K)
    (h : z * (v z * Work.Spaces.w z) ^ 2 ≤ K) :
    v z ^ 2 ≤ K * (min z 1) ^ 2 := by
  -- `w z = (1+z)²/z²`, so `z * w z ^ 2 = (1+z)⁴ / z³`.
  have hz3 : (0 : ℝ) < z ^ 3 := by positivity
  have hzw : z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
    rw [Work.Spaces.w]
    field_simp
  -- The key numeric fact: `1 ≤ (min z 1)² * z * w z ^ 2`, i.e. `z³ ≤ (min z 1)² (1+z)⁴`.
  have hmain : z ^ 3 ≤ (min z 1) ^ 2 * (1 + z) ^ 4 := by
    rcases le_or_gt z 1 with h1 | h1
    · rw [min_eq_left h1]
      have h4 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith) (n := 4)
      have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
      calc z ^ 3 = z ^ 2 * z := by ring
        _ ≤ z ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 hz2
        _ ≤ z ^ 2 * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h4 hz2
    · rw [min_eq_right h1.le]
      have h43 : z ^ 3 ≤ z ^ 4 := by
        calc z ^ 3 = z ^ 3 * 1 := by ring
          _ ≤ z ^ 3 * z := mul_le_mul_of_nonneg_left h1.le (by positivity)
          _ = z ^ 4 := by ring
      have h44 : z ^ 4 ≤ (1 + z) ^ 4 :=
        pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z) (by linarith : z ≤ 1 + z) 4
      linarith
  have hkey : 1 ≤ (min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2) := by
    rw [hzw, ← mul_div_assoc, le_div_iff₀ hz3]
    simpa using hmain
  have hstep : (v z) ^ 2 ≤ (v z) ^ 2 * ((min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hkey (sq_nonneg (v z))
    simpa using this
  calc (v z) ^ 2 ≤ (v z) ^ 2 * ((min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2)) := hstep
    _ = (min z 1) ^ 2 * (z * (v z * Work.Spaces.w z) ^ 2) := by ring
    _ ≤ (min z 1) ^ 2 * K := mul_le_mul_of_nonneg_left h (sq_nonneg (min z 1))
    _ = K * (min z 1) ^ 2 := by ring

end Work.FTS_RXTPieces.noDecayPieces
