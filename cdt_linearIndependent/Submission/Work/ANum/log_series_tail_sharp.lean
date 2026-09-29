import Mathlib

/-! # Sharp tail bound for the odd part of the atanh series

For `|v| ≤ 1/3` the tail `∑_{j≥0} v^(2(j+K)+1)/(2(j+K)+1)` of the odd atanh series is bounded
by `9 / (8·(2K+1)·3^(2K+1))`.  This is the sharp constant (the sibling module
`Work.ANum.log_series_tail_le` records a weaker version with constant `4`).

The proof compares the (absolutely summable) series against the geometric majorant
`|v|^(2K+1)·(|v|²)^j/(2K+1) ≤ (1/3)^(2K+1)·(1/9)^j/(2K+1)`, whose sum is at most
`(1/3)^(2K+1)/((2K+1))·(9/8) = 9/(8·(2K+1)·3^(2K+1))`. -/

namespace Work.ANum

open scoped BigOperators

theorem log_series_tail_sharp {v : ℝ} (hv : |v| ≤ 1 / 3) (K : ℕ) :
    |tsum (fun j : ℕ => v ^ (2 * (j + K) + 1) / ((2 * (j + K) + 1 : ℕ) : ℝ))|
      ≤ 9 / (8 * ((2 * K + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (2 * K + 1)) := by
  have hr0 : 0 ≤ |v| := abs_nonneg v
  have hr1 : |v| < 1 := lt_of_le_of_lt hv (by norm_num)
  have hr2 : |v| ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hr2' : |v| ^ 2 ≤ 1 / 9 := by
    have := pow_le_pow_left₀ hr0 hv 2
    norm_num at this ⊢
    linarith
  have hD0pos : (0 : ℝ) < ((2 * K + 1 : ℕ) : ℝ) := by positivity
  have hD0nonneg : (0 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := hD0pos.le
  set f : ℕ → ℝ := fun j : ℕ => v ^ (2 * (j + K) + 1) / ((2 * (j + K) + 1 : ℕ) : ℝ) with hf
  set a : ℕ → ℝ := fun j : ℕ => |v| ^ (2 * (j + K) + 1) / ((2 * (j + K) + 1 : ℕ) : ℝ) with ha
  set b : ℕ → ℝ := fun j : ℕ =>
    (|v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (|v| ^ 2) ^ j with hb
  have hnorm_f : ∀ j, ‖f j‖ = a j := by
    intro j
    rw [hf, ha, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * (j + K) + 1 : ℕ) : ℝ))]
  have hsumm_g : Summable (fun j : ℕ => (|v| ^ 2) ^ j) :=
    summable_geometric_of_lt_one (pow_nonneg hr0 2) hr2
  have hsumm_b : Summable b := by
    rw [hb]
    exact hsumm_g.mul_left _
  have hle : ∀ j, a j ≤ b j := by
    intro j
    change |v| ^ (2 * (j + K) + 1) / ((2 * (j + K) + 1 : ℕ) : ℝ)
      ≤ (|v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (|v| ^ 2) ^ j
    have hDle : ((2 * K + 1 : ℕ) : ℝ) ≤ ((2 * (j + K) + 1 : ℕ) : ℝ) := by
      have : 2 * K + 1 ≤ 2 * (j + K) + 1 := by omega
      exact_mod_cast this
    have h1 : |v| ^ (2 * (j + K) + 1) = |v| ^ (2 * K + 1) * (|v| ^ 2) ^ j := by
      rw [show 2 * (j + K) + 1 = 2 * K + 1 + 2 * j by ring, pow_add, ← pow_mul]
    rw [h1, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) hD0pos hDle
  have hsumm_a : Summable a :=
    Summable.of_nonneg_of_le (f := b) (g := a) (fun j => by rw [ha]; positivity) hle hsumm_b
  have hsumm_norm : Summable (fun j => ‖f j‖) :=
    hsumm_a.congr (fun j => (hnorm_f j).symm)
  have htsum_le : (∑' j, a j) ≤ ∑' j, b j :=
    Summable.tsum_le_tsum hle hsumm_a hsumm_b
  have hb_val : (∑' j, b j) = (|v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (1 - |v| ^ 2)⁻¹ := by
    rw [hb, tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg hr0 2) hr2]
  have hc_le : |v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)
      ≤ (1 / 3) ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hr0 hv _) hD0nonneg
  have h8 : (8 : ℝ) / 9 ≤ 1 - |v| ^ 2 := by linarith [hr2']
  have hinv_le : (1 - |v| ^ 2)⁻¹ ≤ 9 / 8 := by
    rw [← one_div]
    calc 1 / (1 - |v| ^ 2) ≤ 1 / (8 / 9) := one_div_le_one_div_of_le (by norm_num) h8
      _ = 9 / 8 := by norm_num
  have hinv_nonneg : (0 : ℝ) ≤ (1 - |v| ^ 2)⁻¹ := inv_nonneg.mpr (by linarith [hr2])
  have hc'_nonneg : (0 : ℝ) ≤ (1 / 3) ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ) := by positivity
  have hmul : (|v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (1 - |v| ^ 2)⁻¹
      ≤ ((1 / 3) ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (9 / 8) :=
    mul_le_mul hc_le hinv_le hinv_nonneg hc'_nonneg
  have key : ((1 / 3) ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (9 / 8)
      = 9 / (8 * ((2 * K + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (2 * K + 1)) := by
    rw [one_div_pow]
    field_simp
  calc |tsum f| = ‖tsum f‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ = ∑' j, a j := tsum_congr hnorm_f
    _ ≤ ∑' j, b j := htsum_le
    _ = (|v| ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (1 - |v| ^ 2)⁻¹ := hb_val
    _ ≤ ((1 / 3) ^ (2 * K + 1) / ((2 * K + 1 : ℕ) : ℝ)) * (9 / 8) := hmul
    _ = 9 / (8 * ((2 * K + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (2 * K + 1)) := key

end Work.ANum
