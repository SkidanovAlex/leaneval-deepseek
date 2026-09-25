import Mathlib

namespace Work.LT

/-- For every positive `c` and `a`, for all sufficiently large `D` one has `a*D + 1 ≤ 2^{c*D}`, `2 ≤ a*D` and `1 ≤ D`. -/
theorem gb_D0_large (c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      a * D + 1 ≤ (2 : ℝ) ^ (c * D) ∧ 2 ≤ a * D ∧ 1 ≤ D := by
  -- Exponential `r ^ D` with `r = 2 ^ c > 1` dominates the linear function `(a+1) * D`.
  set r : ℝ := (2 : ℝ) ^ c with hr
  have hr1 : 1 < r := by
    rw [hr]; exact Real.one_lt_rpow (by norm_num) hc
  have hrpos : 0 < r := lt_trans one_pos hr1
  have hlit : (fun n : ℕ => (a + 1) * (n : ℝ)) =o[Filter.atTop] (fun n : ℕ => r ^ n) :=
    (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hr1).const_mul_left (a + 1)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (a + 1) * (n : ℝ) ≤ r ^ n := by
    filter_upwards [hlit.eventuallyLE] with n hn
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg n)),
        Real.norm_of_nonneg (pow_nonneg hrpos.le n)] at hn
    exact hn
  obtain ⟨D1, hD1⟩ := Filter.eventually_atTop.mp hev
  -- Threshold beyond which `2 ≤ a * D`.
  obtain ⟨D2, hD2⟩ := exists_nat_ge (2 / a)
  have hD2' : 2 ≤ a * (D2 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hD2 ha.le
    rwa [mul_div_cancel₀ _ ha.ne'] at this
  refine ⟨max D1 (max D2 1), fun D hD => ?_⟩
  have hDD1 : D1 ≤ D := le_trans (le_max_left _ _) hD
  have hDD2 : D2 ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD
  have hD1le : (1 : ℝ) ≤ D := by
    exact_mod_cast (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hD : 1 ≤ D)
  have hbound : (a + 1) * (D : ℝ) ≤ r ^ D := hD1 D hDD1
  have hrpow : (2 : ℝ) ^ (c * (D : ℝ)) = r ^ D := by
    rw [hr, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrpow]
    have : a * (D : ℝ) + 1 ≤ (a + 1) * (D : ℝ) := by nlinarith
    linarith
  · have : a * (D2 : ℝ) ≤ a * D :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hDD2) ha.le
    linarith
  · exact_mod_cast hD1le

end Work.LT
