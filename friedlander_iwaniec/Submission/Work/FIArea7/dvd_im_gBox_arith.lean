import Mathlib

namespace Work.FIArea7

/-- Arithmetic box bound: from
`N ≤ (4√2·R/L + 1)·(2·Sd·R/m + 1)` together with the box constraints
`R ≤ 2L`, `L ≤ 2(R+1)`, `Sd ≤ √2·L`, `m ≥ 1`, `R ≥ 0` one obtains
`N ≤ 40·((2R+1)^2/m + 1)`.

The proof splits the product into the two factors.  Writing `s = √2`
(so `s^2 = 2`, `0 ≤ s`, `s ≤ 2`):
* `4sR/L + 1 ≤ 8s + 1` using `R ≤ 2L`;
* `2·Sd·R/m + 1 ≤ 4s·R·(R+1)/m + 1` using `Sd ≤ sL` and `L ≤ 2(R+1)`;
then the resulting two-factor product is dominated by `40·((2R+1)^2/m+1)`. -/
theorem dvd_im_gBox_arith {R m L Sd N : ℝ}
    (hR : 0 ≤ R) (hm : 1 ≤ m) (hL : 0 < L) (hSd : 0 ≤ Sd)
    (hLR : R ≤ 2 * L) (hLS : L ≤ 2 * (R + 1)) (hSdL : Sd ≤ Real.sqrt 2 * L)
    (hN : N ≤ (4 * Real.sqrt 2 * R / L + 1) * (2 * Sd * R / m + 1)) :
    N ≤ 40 * (((2 * R + 1) ^ 2) / m + 1) := by
  set s := Real.sqrt 2 with hsdef
  have hs2 : s ^ 2 = 2 := by rw [hsdef]; exact Real.sq_sqrt (by norm_num)
  have hspos : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg 2
  have hsle : s ≤ 2 := by nlinarith [hs2, hspos]
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  -- First factor: `R/L ≤ 2` gives `4sR/L ≤ 8s`.
  have hRL : R / L ≤ 2 := (div_le_iff₀ hL).mpr hLR
  have hA : 4 * s * R / L + 1 ≤ 8 * s + 1 := by
    have h4 : 4 * s * (R / L) ≤ 4 * s * 2 :=
      mul_le_mul_of_nonneg_left hRL (by linarith [hspos])
    rw [show 4 * s * R / L = 4 * s * (R / L) from mul_div_assoc (4 * s) R L]
    linarith
  -- Second factor: `Sd ≤ sL ≤ 2s(R+1)` gives `2·Sd·R ≤ 4s·R·(R+1)`.
  have hB : 2 * Sd * R / m + 1 ≤ 4 * s * R * (R + 1) / m + 1 := by
    have h1 : Sd ≤ s * (2 * (R + 1)) := le_trans hSdL (mul_le_mul_of_nonneg_left hLS hspos)
    have h2 : 2 * R * Sd ≤ 2 * R * (s * (2 * (R + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * R)
    have hnum : 2 * Sd * R ≤ 4 * s * R * (R + 1) := by nlinarith [h2]
    have := (div_le_div_iff_of_pos_right hmpos).mpr hnum
    linarith
  -- Multiply the two bounds.
  have hprod : (4 * s * R / L + 1) * (2 * Sd * R / m + 1) ≤
      (8 * s + 1) * (4 * s * R * (R + 1) / m + 1) := by
    apply mul_le_mul hA hB
    · have : 0 ≤ 2 * Sd * R / m := by positivity
      linarith
    · linarith [hspos]
  -- The dominant product is bounded by `40·((2R+1)^2/m+1)`.
  have hD : (8 * s + 1) * (4 * s * R * (R + 1) / m + 1) ≤
      40 * ((2 * R + 1) ^ 2 / m + 1) := by
    have key : (8 * s + 1) * (4 * s * R * (R + 1) + m) ≤ 40 * ((2 * R + 1) ^ 2 + m) := by
      nlinarith [hs2, hspos, hsle, hR, hm]
    rw [div_add_one (ne_of_gt hmpos), div_add_one (ne_of_gt hmpos)]
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hmpos).mpr key
  calc N ≤ (4 * s * R / L + 1) * (2 * Sd * R / m + 1) := hN
    _ ≤ (8 * s + 1) * (4 * s * R * (R + 1) / m + 1) := hprod
    _ ≤ 40 * ((2 * R + 1) ^ 2 / m + 1) := hD

end Work.FIArea7
