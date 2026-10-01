import Mathlib

namespace Work.ZeroFreeTables.P9

/-- Local quadratic bound: for `‖w‖ ≥ δ/2`, the real part of `-(n / w^2)` is controlled by
`(1 + 4/δ^2) · n/(1 + ‖w‖^2)`, and symmetrically the reciprocal quantity is bounded by
`(1 + 4/δ^2) · ‖n / w^2‖`. -/
theorem zetaQuadLocalBound {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {w : ℂ} (hw : δ / 2 ≤ ‖w‖) :
    (-((n : ℂ) * (1 / w) ^ 2)).re
        ≤ (1 + 4 / δ ^ 2) * ((n : ℝ) * (1 / (1 + ‖w‖ ^ 2))) ∧
      (n : ℝ) * (1 / (1 + ‖w‖ ^ 2)) ≤ (1 + 4 / δ ^ 2) * ‖(n : ℂ) * (1 / w) ^ 2‖ := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hδ2 hw
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- Bound on `-Re ((1/w)^2)`.
  have hA : -(((1 : ℂ) / w) ^ 2).re ≤ 1 / ‖w‖ ^ 2 := by
    rw [← Complex.neg_re]
    calc (-(((1 : ℂ) / w) ^ 2)).re ≤ ‖(-(((1 : ℂ) / w) ^ 2))‖ := Complex.re_le_norm _
      _ = ‖((1 : ℂ) / w) ^ 2‖ := by rw [norm_neg]
      _ = ‖(1 : ℂ) / w‖ ^ 2 := by rw [norm_pow]
      _ = (1 / ‖w‖) ^ 2 := by rw [norm_div, norm_one]
      _ = 1 / ‖w‖ ^ 2 := by rw [one_div, one_div, inv_pow]
  -- Factor out the nonnegative `n`.
  have hB : (-((n : ℂ) * (1 / w) ^ 2)).re = (n : ℝ) * (-(((1 : ℂ) / w) ^ 2).re) := by
    rw [Complex.neg_re, ← Complex.ofReal_natCast n, Complex.re_ofReal_mul]
    ring
  have h1 : (-((n : ℂ) * (1 / w) ^ 2)).re ≤ (n : ℝ) * (1 / ‖w‖ ^ 2) := by
    rw [hB]
    exact mul_le_mul_of_nonneg_left hA hn
  -- The key numerical inequality `1 ≤ (4/δ^2) * ‖w‖^2`.
  have hk : (1 : ℝ) ≤ (4 / δ ^ 2) * ‖w‖ ^ 2 := by
    have hw2 : δ ^ 2 / 4 ≤ ‖w‖ ^ 2 := by
      have h := mul_self_le_mul_self (le_of_lt hδ2) hw
      nlinarith [h]
    have h4 : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
    have h := mul_le_mul_of_nonneg_left hw2 h4
    have heq : (4 / δ ^ 2) * (δ ^ 2 / 4) = 1 := by field_simp
    linarith
  have hmain : 1 / ‖w‖ ^ 2 ≤ (1 + 4 / δ ^ 2) * (1 / (1 + ‖w‖ ^ 2)) := by
    rw [mul_one_div, div_le_div_iff₀ (pow_pos hwpos 2) (by linarith [sq_nonneg ‖w‖])]
    nlinarith [hk, sq_nonneg ‖w‖]
  have hC : (n : ℝ) * (1 / ‖w‖ ^ 2)
      ≤ (1 + 4 / δ ^ 2) * ((n : ℝ) * (1 / (1 + ‖w‖ ^ 2))) := by
    calc (n : ℝ) * (1 / ‖w‖ ^ 2)
        ≤ (n : ℝ) * ((1 + 4 / δ ^ 2) * (1 / (1 + ‖w‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hmain hn
      _ = (1 + 4 / δ ^ 2) * ((n : ℝ) * (1 / (1 + ‖w‖ ^ 2))) := by ring
  -- The normalisation of the second quantity.
  have hnorm : ‖(n : ℂ) * (1 / w) ^ 2‖ = (n : ℝ) * (1 / ‖w‖ ^ 2) := by
    rw [norm_mul, Complex.norm_natCast, norm_pow, norm_div, norm_one]
    rw [one_div, one_div, inv_pow]
  have h4' : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
  have hk1 : (1 : ℝ) ≤ 1 + 4 / δ ^ 2 := by linarith
  have hle : 1 / (1 + ‖w‖ ^ 2) ≤ (1 + 4 / δ ^ 2) * (1 / ‖w‖ ^ 2) := by
    have hb : 1 / (1 + ‖w‖ ^ 2) ≤ 1 / ‖w‖ ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hwpos 2) (by linarith [sq_nonneg ‖w‖])
    calc 1 / (1 + ‖w‖ ^ 2) ≤ 1 / ‖w‖ ^ 2 := hb
      _ = 1 * (1 / ‖w‖ ^ 2) := by ring
      _ ≤ (1 + 4 / δ ^ 2) * (1 / ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hk1 (div_nonneg zero_le_one (sq_nonneg ‖w‖))
  refine ⟨le_trans h1 hC, ?_⟩
  rw [hnorm]
  calc (n : ℝ) * (1 / (1 + ‖w‖ ^ 2))
      ≤ (n : ℝ) * ((1 + 4 / δ ^ 2) * (1 / ‖w‖ ^ 2)) := mul_le_mul_of_nonneg_left hle hn
    _ = (1 + 4 / δ ^ 2) * ((n : ℝ) * (1 / ‖w‖ ^ 2)) := by ring

end Work.ZeroFreeTables.P9
