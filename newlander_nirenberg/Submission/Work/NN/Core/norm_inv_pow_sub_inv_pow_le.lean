import Mathlib

namespace Work.NN.Core

theorem norm_inv_pow_sub_inv_pow_le {e : ℕ} {d : ℝ} (hd : 0 < d) {x y : ℂ}
    (hx : d ≤ ‖x‖) (hy : d ≤ ‖y‖) :
    ‖(x⁻¹) ^ e - (y⁻¹) ^ e‖ ≤ (e : ℝ) * (d⁻¹) ^ (e + 1) * ‖x - y‖ := by
  rcases e with _ | n
  · simp
  have hdnn : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hd hx
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le hd hy
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have hxinv : ‖x⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hxpos hd).mpr hx
  have hyinv : ‖y⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hypos hd).mpr hy
  -- Step B : ‖x⁻¹ - y⁻¹‖ ≤ (d⁻¹)^2 ‖x - y‖
  have hdiff : ‖x⁻¹ - y⁻¹‖ ≤ (d⁻¹) ^ 2 * ‖x - y‖ := by
    rw [inv_sub_inv hx0 hy0, norm_div, norm_mul, norm_sub_rev]
    have hsq : d ^ 2 ≤ ‖x‖ * ‖y‖ := by
      have := mul_le_mul hx hy hd.le (norm_nonneg x)
      rwa [← pow_two] at this
    have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos hxpos hypos
    calc ‖x - y‖ / (‖x‖ * ‖y‖)
        = ‖x - y‖ * (‖x‖ * ‖y‖)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ‖x - y‖ * (d ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left ((inv_le_inv₀ hpos (pow_pos hd 2)).mpr hsq) (norm_nonneg _)
      _ = (d⁻¹) ^ 2 * ‖x - y‖ := by rw [inv_pow]; ring
  -- Step A : telescoping bound on powers of the inverses
  have hpowdiff :
      ‖(x⁻¹) ^ (n + 1) - (y⁻¹) ^ (n + 1)‖ ≤
        ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ n * ‖x⁻¹ - y⁻¹‖ := by
    have hgeom := geom_sum₂_mul (x⁻¹) (y⁻¹) (n + 1)
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖(x⁻¹) ^ i * (y⁻¹) ^ (n + 1 - 1 - i)‖ ≤ (d⁻¹) ^ n := by
      intro i hi
      have hi' : i ≤ n := by
        simp only [Finset.mem_range] at hi
        omega
      rw [norm_mul, norm_pow, norm_pow]
      calc ‖x⁻¹‖ ^ i * ‖y⁻¹‖ ^ (n + 1 - 1 - i)
          ≤ (d⁻¹) ^ i * (d⁻¹) ^ (n + 1 - 1 - i) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxinv i)
              (pow_le_pow_left₀ (norm_nonneg _) hyinv _) (pow_nonneg (norm_nonneg _) _) (pow_nonneg hdnn i)
        _ = (d⁻¹) ^ (i + (n + 1 - 1 - i)) := (pow_add _ _ _).symm
        _ = (d⁻¹) ^ n := by rw [show i + (n + 1 - 1 - i) = n by omega]
    calc ‖(x⁻¹) ^ (n + 1) - (y⁻¹) ^ (n + 1)‖
        = ‖(∑ i ∈ Finset.range (n + 1), (x⁻¹) ^ i * (y⁻¹) ^ (n + 1 - 1 - i)) *
            (x⁻¹ - y⁻¹)‖ := by rw [← hgeom]
      _ = ‖∑ i ∈ Finset.range (n + 1), (x⁻¹) ^ i * (y⁻¹) ^ (n + 1 - 1 - i)‖ *
            ‖x⁻¹ - y⁻¹‖ := norm_mul _ _
      _ ≤ (∑ i ∈ Finset.range (n + 1),
              ‖(x⁻¹) ^ i * (y⁻¹) ^ (n + 1 - 1 - i)‖) * ‖x⁻¹ - y⁻¹‖ :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ (∑ _i ∈ Finset.range (n + 1), (d⁻¹) ^ n) * ‖x⁻¹ - y⁻¹‖ :=
            mul_le_mul_of_nonneg_right (Finset.sum_le_sum hterm) (norm_nonneg _)
      _ = ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ n * ‖x⁻¹ - y⁻¹‖ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfin : ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ n * ((d⁻¹) ^ 2 * ‖x - y‖)
      = ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ (n + 2) * ‖x - y‖ := by
    rw [pow_add]; ring
  calc ‖(x⁻¹) ^ (n + 1) - (y⁻¹) ^ (n + 1)‖
      ≤ ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ n * ‖x⁻¹ - y⁻¹‖ := hpowdiff
    _ ≤ ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ n * ((d⁻¹) ^ 2 * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left hdiff (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hdnn n))
    _ = ((n + 1 : ℕ) : ℝ) * (d⁻¹) ^ (n + 2) * ‖x - y‖ := hfin

end Work.NN.Core
