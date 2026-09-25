import Mathlib

namespace Work.LT

/-- Sharp-factor identity used in the analysis of good locally testable codes:
the difference of powers of two factors through the ratio of the
corresponding geometric-progression tails. -/
theorem gb_sharp_factor {m k : ℕ} (hk : k ≤ m) (i : Fin k) :
    ((2 : ℝ) ^ m - (2 : ℝ) ^ (i : ℕ)) =
      (2 : ℝ) ^ (m - k) * ((2 : ℝ) ^ k - (2 : ℝ) ^ (i : ℕ)) *
        (1 - (1 / 2 : ℝ) ^ (m - (i : ℕ))) / (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ))) := by
  set a := (i : ℕ) with ha_def
  have ha : a < k := i.isLt
  have hak : a ≤ k := le_of_lt ha
  have ham : a ≤ m := le_trans hak hk
  have h1 : (2:ℝ)^a * (2:ℝ)^(k-a) = (2:ℝ)^k := by
    rw [← pow_add, Nat.add_sub_of_le hak]
  have h2 : (2:ℝ)^a * ((2:ℝ)^(k-a) * (2:ℝ)^(m-k)) = (2:ℝ)^m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h3 : (1/2:ℝ)^(k-a) = ((2:ℝ)^(k-a))⁻¹ := by rw [one_div, inv_pow]
  have h4 : (1/2:ℝ)^(m-a) = ((2:ℝ)^(k-a) * (2:ℝ)^(m-k))⁻¹ := by
    have hexp : m - a = (k-a) + (m-k) := by omega
    rw [one_div, inv_pow, hexp, pow_add]
  have hp1 : (2:ℝ)^(k-a) ≠ 1 := by
    have hlt : (1:ℝ) < (2:ℝ)^(k-a) := one_lt_pow₀ (by norm_num) (Nat.sub_ne_zero_of_lt ha)
    exact ne_of_gt hlt
  rw [← h2, ← h1, h3, h4]
  field_simp

end Work.LT
