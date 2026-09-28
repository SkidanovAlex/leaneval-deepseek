import Mathlib

namespace Work.HP.MDEstimates

/-- Arithmetic bound used in the second-moment estimate: if `1 ≤ a, b ≤ Z` and
`0 < A ≤ 4a²`, `0 < B ≤ 4b²`, then
`(1 + Z/a)² (1 + Z/b)² ≤ 256 Z⁴ / (A·B)`.

The proof avoids division by writing `(1 + Z/a)² * a² = (a + Z)² ≤ (2Z)² = 4Z²`
(using `a ≤ Z`), similarly for `b`, and `A·B ≤ 16 a²b²`; multiplying gives
`(1+Z/a)²(1+Z/b)² · A·B ≤ 256 Z⁴`, and the denominators are positive. -/
theorem weight_arith (Z a b A B : ℝ) (hZ : 1 ≤ Z) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hZa : a ≤ Z) (hZb : b ≤ Z) (hA : A ≤ 4 * a ^ 2) (hB : B ≤ 4 * b ^ 2)
    (hApos : 0 < A) (hBpos : 0 < B) :
    (1 + Z / a) ^ 2 * (1 + Z / b) ^ 2 ≤ 256 * Z ^ 4 / (A * B) := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hZpos : 0 < Z := by linarith
  have hra : (1 + Z / a)^2 * a^2 = (a + Z)^2 := by
    have h : (1 + Z / a) = (a + Z) / a := by field_simp
    rw [h]; field_simp
  have hrb : (1 + Z / b)^2 * b^2 = (b + Z)^2 := by
    have h : (1 + Z / b) = (b + Z) / b := by field_simp
    rw [h]; field_simp
  have key_a : (1 + Z / a)^2 * a^2 ≤ 4 * Z^2 := by
    rw [hra]
    have hle : a + Z ≤ 2 * Z := by linarith
    have hnn : 0 ≤ a + Z := by linarith
    calc (a + Z)^2 ≤ (2*Z)^2 := pow_le_pow_left₀ hnn hle 2
      _ = 4 * Z^2 := by ring
  have key_b : (1 + Z / b)^2 * b^2 ≤ 4 * Z^2 := by
    rw [hrb]
    have hle : b + Z ≤ 2 * Z := by linarith
    have hnn : 0 ≤ b + Z := by linarith
    calc (b + Z)^2 ≤ (2*Z)^2 := pow_le_pow_left₀ hnn hle 2
      _ = 4 * Z^2 := by ring
  have hAB : A * B ≤ 16 * a^2 * b^2 := by
    nlinarith [mul_le_mul hA hB hBpos.le (by positivity : (0:ℝ) ≤ 4 * a^2)]
  have hprod : ((1 + Z / a)^2 * a^2) * ((1 + Z / b)^2 * b^2) ≤ (4*Z^2)*(4*Z^2) :=
    mul_le_mul key_a key_b (by positivity) (by positivity)
  have hmain : (1 + Z / a)^2 * (1 + Z / b)^2 * (A * B) ≤ 256 * Z^4 := by
    have e1 : (1 + Z / a)^2 * (1 + Z / b)^2 * (A * B)
        ≤ (1 + Z / a)^2 * (1 + Z / b)^2 * (16 * a^2 * b^2) :=
      mul_le_mul_of_nonneg_left hAB (by positivity)
    have e2 : (1 + Z / a)^2 * (1 + Z / b)^2 * (16 * a^2 * b^2)
        = 16 * (((1 + Z / a)^2 * a^2) * ((1 + Z / b)^2 * b^2)) := by ring
    have e3 : 16 * (((1 + Z / a)^2 * a^2) * ((1 + Z / b)^2 * b^2))
        ≤ 16 * ((4*Z^2)*(4*Z^2)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    have e4 : 16 * ((4*Z^2)*(4*Z^2)) = 256 * Z^4 := by ring
    linarith
  rw [le_div_iff₀ (by positivity : 0 < A * B)]
  exact hmain

end Work.HP.MDEstimates
