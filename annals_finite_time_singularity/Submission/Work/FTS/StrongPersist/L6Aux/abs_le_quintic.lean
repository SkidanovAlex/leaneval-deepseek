import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A crude bound for a quintic polynomial by its coefficient `ℓ¹`-norm

For `z ≥ 0` and arbitrary real coefficients `s, b, c, d, e, f`,

`|s z⁵ + b z⁴ + c z³ + d z² + e z + f| ≤ (|s|+|b|+|c|+|d|+|e|+|f|) (1+z)⁵`.

The proof is the triangle inequality, termwise, together with the pointwise bounds
`z ^ k ≤ (1 + z) ^ 5` for `0 ≤ z` and `k ≤ 5` (both `z ≤ 1 + z` and `(1 + z) ^ k ≤ (1 + z) ^ 5`
follow from `1 ≤ 1 + z`).
-/

namespace Work.FTS.StrongPersist.L6Aux

/-- `z ^ k ≤ (1 + z) ^ 5` for `z ≥ 0` and `k ≤ 5`. -/
private lemma pow_le_one_add_pow_five {z : ℝ} (hz : 0 ≤ z) {k : ℕ} (hk : k ≤ 5) :
    z ^ k ≤ (1 + z) ^ 5 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have hzle : z ≤ 1 + z := by linarith
  calc z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz hzle k
    _ ≤ (1 + z) ^ 5 := pow_le_pow_right₀ h1z hk

theorem abs_le_quintic (z s b c d e f : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z + f|
      ≤ (|s| + |b| + |c| + |d| + |e| + |f|) * (1 + z) ^ 5 := by
  have hzn : (0 : ℝ) ≤ z := hz
  have hP : (1 : ℝ) ≤ (1 + z) ^ 5 := by
    have := pow_le_one_add_pow_five hz (show (0 : ℕ) ≤ 5 by norm_num)
    simpa using this
  -- termwise bounds
  have hA : |s * z ^ 5| ≤ |s| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 5)]
    exact mul_le_mul_of_nonneg_left (pow_le_one_add_pow_five hz le_rfl) (abs_nonneg s)
  have hB : |b * z ^ 4| ≤ |b| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 4)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg b)
  have hC : |c * z ^ 3| ≤ |c| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 3)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg c)
  have hD : |d * z ^ 2| ≤ |d| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg d)
  have hE : |e * z| ≤ |e| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg hzn]
    exact mul_le_mul_of_nonneg_left
      (by simpa using pow_le_one_add_pow_five hz (show (1 : ℕ) ≤ 5 by norm_num))
      (abs_nonneg e)
  have hF : |f| ≤ |f| * (1 + z) ^ 5 := le_mul_of_one_le_right (abs_nonneg f) hP
  -- triangle inequality, peeled off one term at a time
  have t1 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z + f|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z| + |f| := abs_add_le _ _
  have t2 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2| + |e * z| := abs_add_le _ _
  have t3 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3| + |d * z ^ 2| := abs_add_le _ _
  have t4 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3|
      ≤ |s * z ^ 5 + b * z ^ 4| + |c * z ^ 3| := abs_add_le _ _
  have t5 : |s * z ^ 5 + b * z ^ 4| ≤ |s * z ^ 5| + |b * z ^ 4| := abs_add_le _ _
  have hX : (|s| + |b| + |c| + |d| + |e| + |f|) * (1 + z) ^ 5
      = (|s| * (1 + z) ^ 5 + |b| * (1 + z) ^ 5 + |c| * (1 + z) ^ 5
          + |d| * (1 + z) ^ 5 + |e| * (1 + z) ^ 5) + |f| * (1 + z) ^ 5 := by ring
  linarith [t1, t2, t3, t4, t5, hA, hB, hC, hD, hE, hF, hX]

end Work.FTS.StrongPersist.L6Aux
