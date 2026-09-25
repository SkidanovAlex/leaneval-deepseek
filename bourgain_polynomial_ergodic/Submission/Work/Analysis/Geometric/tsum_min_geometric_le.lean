import Mathlib

namespace Work.Analysis.Geometric

/-- For `r > 1` and `A ≥ 0`, the series `∑ᵢ min (A rⁱ) (A⁻¹ r⁻ⁱ)` converges, and its sum is
bounded by `2r/(r-1)` uniformly in `A`. -/
theorem tsum_min_geometric_le (r A : ℝ) (hr : 1 < r) (hA : 0 ≤ A) :
    Summable (fun i : ℕ => min (A * r^i) (A⁻¹ * (r⁻¹)^i)) ∧
    ∑' i : ℕ, min (A * r^i) (A⁻¹ * (r⁻¹)^i) ≤ 2 * r / (r - 1) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr1 : 0 < r - 1 := by linarith
  have hrne : r ≠ 1 := ne_of_gt hr
  have hqlt : ‖r⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    exact inv_lt_one_of_one_lt₀ hr
  have hqsumm : Summable (fun i : ℕ => (r⁻¹)^i) := summable_geometric_of_norm_lt_one hqlt
  have hnonneg : ∀ i : ℕ, 0 ≤ min (A * r^i) (A⁻¹ * (r⁻¹)^i) := by
    intro i
    exact le_min (by positivity) (by positivity)
  have hsumm : Summable fun i : ℕ => min (A * r^i) (A⁻¹ * (r⁻¹)^i) :=
    Summable.of_nonneg_of_le hnonneg (fun i => min_le_right _ _) (hqsumm.mul_left A⁻¹)
  refine ⟨hsumm, ?_⟩
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hz : (fun i : ℕ => min (A * r^i) (A⁻¹ * (r⁻¹)^i)) = fun _ => (0:ℝ) := by
      funext i; rw [← hA0]; simp
    rw [hz, tsum_zero]
    positivity
  · -- `m` is the first index where `A r^m ≥ 1`
    have hnex : ∃ n : ℕ, 1 ≤ A * r^n := by
      have htend := tendsto_pow_atTop_atTop_of_one_lt hr
      have hev : ∀ᶠ n : ℕ in Filter.atTop, A⁻¹ ≤ r^n :=
        htend.eventually (Filter.eventually_ge_atTop A⁻¹)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨n, hn⟩ := hev
      refine ⟨n, ?_⟩
      have h := hn n le_rfl
      have h2 : A * A⁻¹ ≤ A * r^n := mul_le_mul_of_nonneg_left h hApos.le
      simpa [mul_inv_cancel₀ (ne_of_gt hApos)] using h2
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, 1 ≤ A * r^m ∧ ∀ j < m, ¬ (1 ≤ A * r^j) :=
      ⟨Nat.find hnex, Nat.find_spec hnex, fun j hj => Nat.find_min hnex hj⟩
    have hsplit := hsumm.sum_add_tsum_nat_add m
    -- on `[0, m)` the min is dominated by `A r^i`, and `A r^m ≤ r`
    have hpart1 : ∑ i ∈ Finset.range m, min (A * r^i) (A⁻¹ * (r⁻¹)^i) ≤ r / (r - 1) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0]; simp only [Finset.range_zero, Finset.sum_empty]; positivity
      · have hm1 : A * r^m ≤ r := by
          have hlt : A * r^(m-1) < 1 :=
            not_le.mp (hmin (m - 1) (Nat.sub_lt hmpos one_pos))
          have hpow : r^m = r^(m-1) * r := by
            conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m from hmpos)]
            rw [pow_add, pow_one]
          rw [hpow]
          calc A * (r^(m-1) * r) = (A * r^(m-1)) * r := by ring
            _ ≤ 1 * r := mul_le_mul_of_nonneg_right hlt.le hr0.le
            _ = r := one_mul r
        calc ∑ i ∈ Finset.range m, min (A * r^i) (A⁻¹ * (r⁻¹)^i)
            ≤ ∑ i ∈ Finset.range m, A * r^i := Finset.sum_le_sum (fun i _ => min_le_left _ _)
          _ = A * ∑ i ∈ Finset.range m, r^i := (Finset.mul_sum _ _ _).symm
          _ = A * ((r^m - 1) / (r - 1)) := by rw [geom_sum_eq hrne]
          _ ≤ r / (r - 1) := by
              rw [← mul_div_assoc]
              exact div_le_div_of_nonneg_right
                (le_trans (mul_le_mul_of_nonneg_left (by linarith : r^m - 1 ≤ r^m) hApos.le) hm1) hr1.le
    -- on `[m, ∞)` the min is dominated by `A⁻¹ r^{-i}`, whose tail is bounded by `1`
    have hshift : Summable (fun i : ℕ => A⁻¹ * (r⁻¹)^(i+m)) := by
      have heq : (fun i : ℕ => A⁻¹ * (r⁻¹)^(i+m)) = fun i => (A⁻¹ * (r⁻¹)^m) * (r⁻¹)^i := by
        funext i; rw [pow_add]; ring
      rw [heq]; exact hqsumm.mul_left _
    have hpart2 : ∑' i : ℕ, min (A * r^(i+m)) (A⁻¹ * (r⁻¹)^(i+m)) ≤ r / (r - 1) := by
      have h1 : ∑' i : ℕ, min (A * r^(i+m)) (A⁻¹ * (r⁻¹)^(i+m))
          ≤ ∑' i : ℕ, A⁻¹ * (r⁻¹)^(i+m) :=
        Summable.tsum_le_tsum (fun i => min_le_right _ _)
          (hsumm.comp_injective (add_left_injective m)) hshift
      calc ∑' i : ℕ, min (A * r^(i+m)) (A⁻¹ * (r⁻¹)^(i+m))
          ≤ ∑' i : ℕ, A⁻¹ * (r⁻¹)^(i+m) := h1
        _ = ∑' i : ℕ, (A⁻¹ * (r⁻¹)^m) * (r⁻¹)^i := by
              apply tsum_congr; intro i; rw [pow_add]; ring
        _ = (A⁻¹ * (r⁻¹)^m) * ∑' i : ℕ, (r⁻¹)^i := tsum_mul_left
        _ = (A⁻¹ * (r⁻¹)^m) * (1 - r⁻¹)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hqlt]
        _ ≤ r / (r - 1) := by
            have hc : A⁻¹ * (r⁻¹)^m ≤ 1 := by
              have hrm : 0 < r^m := pow_pos hr0 m
              have hinv : A⁻¹ ≤ r^m := by
                have h2 : A⁻¹ * 1 ≤ A⁻¹ * (A * r^m) :=
                  mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hApos.le)
                rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hApos), one_mul] at h2
              calc A⁻¹ * (r⁻¹)^m = A⁻¹ * (r^m)⁻¹ := by rw [inv_pow]
                _ ≤ r^m * (r^m)⁻¹ := mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hrm.le)
                _ = 1 := mul_inv_cancel₀ (ne_of_gt hrm)
            have hpos : 0 < (1 - r⁻¹)⁻¹ := by
              apply inv_pos.mpr
              have := inv_lt_one_of_one_lt₀ hr
              linarith
            calc (A⁻¹ * (r⁻¹)^m) * (1 - r⁻¹)⁻¹ ≤ 1 * (1 - r⁻¹)⁻¹ :=
                  mul_le_mul_of_nonneg_right hc hpos.le
              _ = (1 - r⁻¹)⁻¹ := one_mul _
              _ = r / (r - 1) := by
                  have hd : 1 - r⁻¹ = (r - 1)/r := by field_simp
                  rw [hd, inv_div]
    calc ∑' i : ℕ, min (A * r^i) (A⁻¹ * (r⁻¹)^i)
        = (∑ i ∈ Finset.range m, min (A * r^i) (A⁻¹ * (r⁻¹)^i))
            + ∑' i : ℕ, min (A * r^(i+m)) (A⁻¹ * (r⁻¹)^(i+m)) := hsplit.symm
      _ ≤ r / (r - 1) + r / (r - 1) := add_le_add hpart1 hpart2
      _ = 2 * r / (r - 1) := by rw [← two_mul, mul_div_assoc]

end Work.Analysis.Geometric
