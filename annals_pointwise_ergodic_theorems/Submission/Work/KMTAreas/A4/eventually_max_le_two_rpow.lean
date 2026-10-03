import Mathlib

open Filter

namespace Work.KMTAreas.A4

/-- For `a > 0` and any real `X`, the exponential `2 ^ (a * l)` eventually dominates both
the constant `X` and the linear term `l + 1`. Equivalently: `2 ^ (a * ·)` tends to `+∞`
faster than `l ↦ l + 1`, so the maximum of the two is eventually below it. -/
theorem eventually_max_le_two_rpow (a X : ℝ) (ha : 0 < a) :
    ∀ᶠ l : ℕ in Filter.atTop, max X ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (a * (l : ℝ)) := by
  set c : ℝ := (2 : ℝ) ^ a with hcdef
  have hc1 : 1 < c := by rw [hcdef]; exact Real.one_lt_rpow (by norm_num) ha
  have hcpos : 0 < c := lt_trans one_pos hc1
  -- `c ^ l → +∞`, hence eventually dominates the constant `X`
  have hX : ∀ᶠ l : ℕ in Filter.atTop, X ≤ c ^ l :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).eventually_ge_atTop X
  -- `l / c ^ l → 0` (the exponential beats the linear term)
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) / c ^ n) Filter.atTop (nhds 0) :=
    (isLittleO_coe_const_pow_of_one_lt hc1).tendsto_div_nhds_zero
  have hlin : ∀ᶠ l : ℕ in Filter.atTop, (l : ℝ) + 1 ≤ c ^ l := by
    filter_upwards [hdiv.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      Filter.eventually_ge_atTop (1 : ℕ)] with l hl h1
    have hl' : (l : ℝ) / c ^ l ≤ 1 / 2 := hl
    have hcposl : 0 < c ^ l := pow_pos hcpos l
    have hl2 : (l : ℝ) ≤ (1 / 2) * c ^ l := (div_le_iff₀ hcposl).mp hl'
    have h1l : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast h1
    nlinarith
  filter_upwards [hX, hlin] with l hXl hlinl
  have hpow : c ^ l = (2 : ℝ) ^ (a * (l : ℝ)) := by
    rw [hcdef, ← Real.rpow_natCast ((2 : ℝ) ^ a) l,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hpow] at hXl hlinl
  exact max_le hXl hlinl

end Work.KMTAreas.A4
