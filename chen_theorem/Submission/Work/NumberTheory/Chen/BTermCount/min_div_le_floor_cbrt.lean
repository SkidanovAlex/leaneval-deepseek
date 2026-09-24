import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- The `q`-range of the `B`-term sum never reaches `(x+2)^{1/3}`: with `Y ≥ x^{1/3}`,
`min (Y−1) ⌊(x+2)/Y²⌋ ≤ ⌊(x+2)^{1/3}⌋`.
(If `m = ⌊(x+2)^{1/3}⌋ < min (Y−1) ⌊(x+2)/Y²⌋` then `Y ≥ m+2 > (x+2)^{1/3}`, so
`(x+2)/Y² < (x+2)^{1/3}`, whence `⌊(x+2)/Y²⌋ ≤ m < min (Y−1) ⌊(x+2)/Y²⌋`, a contradiction.) -/
theorem min_div_le_floor_cbrt (x Y : ℕ) (hx : 1 ≤ x) (hY : (x : ℝ) ^ ((1:ℝ)/3) ≤ (Y : ℝ)) :
    min (Y - 1) ((x + 2) / (Y * Y)) ≤ ⌊((x : ℝ) + 2) ^ ((1:ℝ)/3)⌋₊ := by
  set a : ℝ := (x : ℝ) + 2 with ha_def
  set c : ℝ := a ^ ((1:ℝ)/3) with hc_def
  set m : ℕ := ⌊c⌋₊ with hm_def
  have ha_pos : 0 < a := by
    rw [ha_def]; positivity
  have hc_pos : 0 < c := by
    rw [hc_def]; exact Real.rpow_pos_of_pos ha_pos _
  have hc3 : c ^ 3 = a := by
    rw [hc_def]
    have h : ((1:ℝ)/3) = ((3:ℕ):ℝ)⁻¹ := by norm_num
    rw [h]
    exact Real.rpow_inv_natCast_pow (le_of_lt ha_pos) (by norm_num)
  by_cases h : Y - 1 ≤ m
  · exact le_trans (min_le_left _ _) h
  · have hlt : m < Y - 1 := not_le.mp h
    have hYge : m + 2 ≤ Y := by
      have h1 : m + 1 < Y := (Nat.lt_sub_iff_add_lt).mp hlt
      omega
    have hYpos : (0:ℝ) < (Y:ℝ) := by
      have : 0 < Y := by omega
      exact_mod_cast this
    have hc_lt_Y : c < (Y:ℝ) := by
      have h1 : c < (m:ℝ) + 1 := by
        have := Nat.lt_floor_add_one c
        rw [← hm_def] at this
        exact this
      have h2 : ((m:ℝ) + 2) ≤ (Y:ℝ) := by
        have hh := Nat.cast_le (α := ℝ).mpr hYge
        push_cast at hh
        linarith
      linarith
    have hc2_lt : c ^ 2 < (Y:ℝ) ^ 2 :=
      pow_lt_pow_left₀ hc_lt_Y (le_of_lt hc_pos) (by norm_num : (2:ℕ) ≠ 0)
    have hmain : a < c * (Y:ℝ)^2 := by
      rw [← hc3, show c ^ 3 = c * c ^ 2 by ring]
      exact mul_lt_mul_of_pos_left hc2_lt hc_pos
    have hdiv : a / (Y:ℝ)^2 < c := by
      rw [div_lt_iff₀ (pow_pos hYpos 2)]
      exact hmain
    have hcast : (((x + 2) / (Y * Y) : ℕ) : ℝ) ≤ a / (Y:ℝ)^2 := by
      have h1 : (((x + 2) / (Y * Y) : ℕ) : ℝ) ≤ ((x + 2 : ℕ) : ℝ) / ((Y * Y : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h2 : ((x + 2 : ℕ) : ℝ) = a := by rw [ha_def]; push_cast; ring
      have h3 : ((Y * Y : ℕ) : ℝ) = (Y:ℝ)^2 := by push_cast; ring
      rw [h2, h3] at h1
      exact h1
    have hn_lt : (((x + 2) / (Y * Y) : ℕ) : ℝ) < c := lt_of_le_of_lt hcast hdiv
    have hn_le : ((x + 2) / (Y * Y) : ℕ) ≤ m := by
      have h1 : (((x + 2) / (Y * Y) : ℕ) : ℝ) < (m:ℝ) + 1 := by
        have := Nat.lt_floor_add_one c
        rw [← hm_def] at this
        linarith
      have h2 : ((x + 2) / (Y * Y) : ℕ) < m + 1 := by exact_mod_cast h1
      omega
    exact le_trans (min_le_right _ _) hn_le

end Work.NumberTheory.Chen.BTermCount
