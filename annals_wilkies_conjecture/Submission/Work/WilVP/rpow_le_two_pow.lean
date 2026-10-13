import Mathlib

namespace Work.WilVP

/-- For `1/2 < t < 2` and `|q| ≤ Qb`, the real power `t ^ q` is bounded by `2 ^ Qb`.
The key point is that both `t` and `t⁻¹` are bounded by `2`, so `t ^ q ≤ 2 ^ |q| ≤ 2 ^ Qb`. -/
lemma rpow_le_two_pow {t q : ℝ} {Qb : ℕ} (ht1 : 1/2 < t) (ht2 : t < 2)
    (hq : |q| ≤ (Qb : ℝ)) : t ^ q ≤ (2 : ℝ) ^ Qb := by
  have ht0 : 0 < t := by linarith
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  have haq : (0 : ℝ) ≤ |q| := abs_nonneg q
  have hint : t ^ q ≤ (2 : ℝ) ^ |q| := by
    rcases le_total 1 t with h1 | h1
    · -- `t ≥ 1`: `t ^ q ≤ t ^ |q| ≤ 2 ^ |q|`
      calc t ^ q ≤ t ^ |q| := Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self q)
        _ ≤ (2 : ℝ) ^ |q| := Real.rpow_le_rpow (by linarith) (le_of_lt ht2) haq
    · -- `t ≤ 1`: `t ^ q ≤ t ^ (-|q|) = (t⁻¹) ^ |q| ≤ 2 ^ |q|`
      have hq' : t ^ q ≤ t ^ (-|q|) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 h1 (neg_abs_le q)
      have hinv : t⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ ht0]
        linarith
      calc t ^ q ≤ t ^ (-|q|) := hq'
        _ = t⁻¹ ^ |q| := Real.rpow_neg_eq_inv_rpow t |q|
        _ ≤ (2 : ℝ) ^ |q| := Real.rpow_le_rpow (inv_nonneg.mpr ht0.le) hinv haq
  calc t ^ q ≤ (2 : ℝ) ^ |q| := hint
    _ ≤ (2 : ℝ) ^ (Qb : ℝ) := Real.rpow_le_rpow_of_exponent_le h2 hq
    _ = (2 : ℝ) ^ Qb := Real.rpow_natCast 2 Qb

end Work.WilVP
