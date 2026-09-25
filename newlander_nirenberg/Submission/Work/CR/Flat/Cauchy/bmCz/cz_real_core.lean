import Mathlib

namespace Work.CR.Flat.Cauchy.bmCz

/-- Scalar comparison lemma used to combine the two Bochner–Martinelli error terms.

Writing `x = X`, `y = Y`, `h = H`, the two error terms on the left are

* `(5/2) * x * h / x^m = (5/2) * h * x^(1-m)`, and
* `m * (3x/2)^(m-1) * h * y^2 / (x^m y^m) = m * (3/2)^(m-1) * h * x^(-1) * y^(2-m)`,

while the right hand side is `(5/2 + m * (3/2)^(m-1) * 2^(m-2)) * h * x^(1-m)`.
The first terms agree exactly, and the second reduce to `(x/y)^(m-2) ≤ 2^(m-2)`,
which holds because `x ≤ 2y`. -/
theorem cz_real_core {m : ℕ} (hm : 2 ≤ m) {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 ≤ H) (hXY : |X - Y| ≤ H) (hYe : X ≤ 2 * Y) (hYu : 2 * Y ≤ 3 * X) :
    (5 / 2) * X * H / X ^ m + (m : ℝ) * (3 * X / 2) ^ (m - 1) * H * Y ^ 2 / (X ^ m * Y ^ m)
      ≤ (5 / 2 + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2)) * H * (X ^ (m - 1))⁻¹ := by
  -- The first term is already in the desired normal form.
  have h1 : (5 / 2) * X * H / X ^ m = (5 / 2) * H * (X ^ (m - 1))⁻¹ := by
    have hXm : X ^ m = X ^ (m - 1) * X := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
    rw [hXm]
    field_simp
  -- The second term is bounded by the corresponding term on the right.
  have h2 : (m : ℝ) * (3 * X / 2) ^ (m - 1) * H * Y ^ 2 / (X ^ m * Y ^ m)
      ≤ (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2) * H * (X ^ (m - 1))⁻¹ := by
    have hp1 : (3 * X / 2) ^ (m - 1) = (3 / 2) ^ (m - 1) * X ^ (m - 1) := by
      rw [show (3 * X / 2) = (3 / 2) * X by ring, mul_pow]
    have hXm : X ^ m = X ^ (m - 1) * X := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
    have hYm : Y ^ m = Y ^ 2 * Y ^ (m - 2) := by
      conv_lhs => rw [show m = 2 + (m - 2) by omega]
      rw [pow_add]
    have key : X ^ (m - 2) ≤ 2 ^ (m - 2) * Y ^ (m - 2) := by
      have h : X ^ (m - 2) ≤ (2 * Y) ^ (m - 2) := pow_le_pow_left₀ (le_of_lt hX) hYe _
      rwa [mul_pow] at h
    have hXsq : X ^ (m - 1) = X * X ^ (m - 2) := by
      conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega]
      rw [pow_succ, mul_comm]
    rw [hp1, hXm, hYm]
    field_simp
    rw [hXsq]
    have hHX : (0 : ℝ) ≤ H * X := mul_nonneg hH (le_of_lt hX)
    calc X * X ^ (m - 2) * H = H * X * X ^ (m - 2) := by ring
      _ ≤ H * X * (2 ^ (m - 2) * Y ^ (m - 2)) := mul_le_mul_of_nonneg_left key hHX
      _ = H * X * Y ^ (m - 2) * 2 ^ (m - 2) := by ring
  calc
    (5 / 2) * X * H / X ^ m + (m : ℝ) * (3 * X / 2) ^ (m - 1) * H * Y ^ 2 / (X ^ m * Y ^ m)
        ≤ (5 / 2) * H * (X ^ (m - 1))⁻¹
            + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2) * H * (X ^ (m - 1))⁻¹ :=
          add_le_add h1.le h2
    _ = (5 / 2 + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2)) * H * (X ^ (m - 1))⁻¹ := by
          ring

end Work.CR.Flat.Cauchy.bmCz
