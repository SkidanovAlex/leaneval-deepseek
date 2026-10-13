import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem sum_sq_first_le (k : ℕ) (a : ℕ → ℝ) (w s η : ℝ)
    (hη0 : 0 < η) (hη2 : η ≤ 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑ i ∈ Finset.range (k + 1), (a i * s * (w / s ^ (η / 2))) ^ 2)
      ≤ w ^ 2 * ∑ i ∈ Finset.range (k + 1), (a i) ^ 2 := by
  have hη2pos : 0 < η / 2 := by linarith
  have hη2le : η / 2 ≤ 1 := by linarith
  -- Pointwise core bound: `(s * (w / s^(η/2)))^2 ≤ w^2`.
  have hkey : (s * (w / s ^ (η / 2))) ^ 2 ≤ w ^ 2 := by
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs]
      have hz : (0:ℝ) ^ (η/2) = 0 := Real.zero_rpow (ne_of_gt hη2pos)
      rw [hz]
      norm_num
      positivity
    · have hspos : 0 < s := hs
      have hden : 0 < s ^ (η/2) := Real.rpow_pos_of_pos hspos _
      have hle : s ≤ s ^ (η/2) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hspos hs1 hη2le
        simpa using h
      have hratio0 : 0 ≤ s / s ^ (η/2) := div_nonneg hs0 (le_of_lt hden)
      have hratio1 : s / s ^ (η/2) ≤ 1 := by
        rw [div_le_iff₀ hden]
        simpa using hle
      rw [sq_le_sq]
      have heq : s * (w / s ^ (η / 2)) = (s / s ^ (η / 2)) * w := by ring
      rw [heq, abs_mul, abs_of_nonneg hratio0]
      calc (s / s ^ (η / 2)) * |w|
          ≤ 1 * |w| := mul_le_mul_of_nonneg_right hratio1 (abs_nonneg w)
        _ = |w| := one_mul _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc (a i * s * (w / s ^ (η / 2))) ^ 2
      = (a i)^2 * (s * (w / s ^ (η/2)))^2 := by ring
    _ ≤ (a i)^2 * w^2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = w^2 * (a i)^2 := by ring

end Work.FTS.EllipticEst
