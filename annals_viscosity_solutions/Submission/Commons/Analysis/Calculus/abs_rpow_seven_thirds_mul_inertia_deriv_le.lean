import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Calculus

theorem abs_rpow_seven_thirds_mul_inertia_deriv_le {D1 D2 D3 I t b1 b2 b3 b4 b5 b6 : ℝ} (ht : 0 < t) (hI : 0 < I) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (h3 : 0 ≤ b3) (h4 : 0 ≤ b4) (h5 : 0 ≤ b5) (h6 : 0 ≤ b6) (hD1 : |D1 / t ^ ((1:ℝ)/3)| ≤ b1) (hD2 : |D2 * t ^ ((2:ℝ)/3)| ≤ b2) (hD3 : |t ^ ((5:ℝ)/3) * D3| ≤ b3) (hs : |t ^ ((2:ℝ)/3) / Real.sqrt I| ≤ b4) (hq3 : |(I / t ^ ((4:ℝ)/3)) ^ (-((3:ℝ)/2))| ≤ b5) (hq5 : |(I / t ^ ((4:ℝ)/3)) ^ (-((5:ℝ)/2))| ≤ b6) : |t ^ ((7:ℝ)/3) * (D3 / (2 * Real.sqrt I) - 3 * D1 * D2 / (4 * (Real.sqrt I) ^ 3) + 3 * D1 ^ 3 / (8 * (Real.sqrt I) ^ 5))| ≤ b3 * b4 / 2 + 3 / 4 * (b1 * b2 * b5) + 3 / 8 * (b1 ^ 3 * b6) := by
  have hsqI : 0 < Real.sqrt I := Real.sqrt_pos_of_pos hI
  -- auxiliary power identities for the `(1/2)`-rpow expressions
  have hP_eq : (I / t ^ ((4:ℝ)/3)) ^ (-((3:ℝ)/2)) = t^2 / (Real.sqrt I)^3 := by
    have htpos : 0 < t ^ ((4:ℝ)/3) := Real.rpow_pos_of_pos ht _
    have h1' : (t ^ ((4:ℝ)/3)) ^ ((3:ℝ)/2) = t^2 := by
      rw [← Real.rpow_mul (le_of_lt ht)]; norm_num
    have h2' : I ^ ((3:ℝ)/2) = (Real.sqrt I)^3 := by
      rw [show (3:ℝ)/2 = (1/2:ℝ)*3 by norm_num, Real.rpow_mul (le_of_lt hI), Real.sqrt_eq_rpow]
      norm_num
    rw [Real.rpow_neg (le_of_lt (div_pos hI htpos)), Real.div_rpow (le_of_lt hI) (le_of_lt htpos), h1', h2', inv_div]
  have hQ_eq : (I / t ^ ((4:ℝ)/3)) ^ (-((5:ℝ)/2)) = t ^ ((10:ℝ)/3) / (Real.sqrt I)^5 := by
    have htpos : 0 < t ^ ((4:ℝ)/3) := Real.rpow_pos_of_pos ht _
    have h1' : (t ^ ((4:ℝ)/3)) ^ ((5:ℝ)/2) = t ^ ((10:ℝ)/3) := by
      rw [← Real.rpow_mul (le_of_lt ht)]; norm_num
    have h2' : I ^ ((5:ℝ)/2) = (Real.sqrt I)^5 := by
      rw [show (5:ℝ)/2 = (1/2:ℝ)*5 by norm_num, Real.rpow_mul (le_of_lt hI), Real.sqrt_eq_rpow]
      norm_num
    rw [Real.rpow_neg (le_of_lt (div_pos hI htpos)), Real.div_rpow (le_of_lt hI) (le_of_lt htpos), h1', h2', inv_div]
  have hP : |t^2 / (Real.sqrt I)^3| ≤ b5 := by simpa [hP_eq] using hq3
  have hQ : |t ^ ((10:ℝ)/3) / (Real.sqrt I)^5| ≤ b6 := by simpa [hQ_eq] using hq5
  -- the algebraic decomposition
  have key : t ^ ((7:ℝ)/3) * (D3 / (2 * Real.sqrt I) - 3 * D1 * D2 / (4 * (Real.sqrt I) ^ 3) + 3 * D1 ^ 3 / (8 * (Real.sqrt I) ^ 5))
      = (t ^ ((5:ℝ)/3) * D3) * (t ^ ((2:ℝ)/3) / Real.sqrt I) / 2
        - (3/4) * ((D1 / t ^ ((1:ℝ)/3)) * (D2 * t ^ ((2:ℝ)/3)) * (t^2 / (Real.sqrt I)^3))
        + (3/8) * ((D1 / t ^ ((1:ℝ)/3))^3 * (t ^ ((10:ℝ)/3) / (Real.sqrt I)^5)) := by
    let u := t ^ ((1:ℝ)/3)
    have hu : u ≠ 0 := by dsimp [u]; exact ne_of_gt (Real.rpow_pos_of_pos ht _)
    have ht1 : t ^ ((1:ℝ)/3) = u := rfl
    have ht2 : t ^ ((2:ℝ)/3) = u^2 := by
      rw [show (2:ℝ)/3 = (1/3:ℝ)*2 by norm_num, Real.rpow_mul (le_of_lt ht)]
      exact Real.rpow_natCast _ 2
    have ht5 : t ^ ((5:ℝ)/3) = u^5 := by
      rw [show (5:ℝ)/3 = (1/3:ℝ)*5 by norm_num, Real.rpow_mul (le_of_lt ht)]
      exact Real.rpow_natCast _ 5
    have ht7 : t ^ ((7:ℝ)/3) = u^7 := by
      rw [show (7:ℝ)/3 = (1/3:ℝ)*7 by norm_num, Real.rpow_mul (le_of_lt ht)]
      exact Real.rpow_natCast _ 7
    have ht10 : t ^ ((10:ℝ)/3) = u^10 := by
      rw [show (10:ℝ)/3 = (1/3:ℝ)*10 by norm_num, Real.rpow_mul (le_of_lt ht)]
      exact Real.rpow_natCast _ 10
    have hthree : t = u^3 := by
      rw [show t = t ^ ((1:ℝ)) by rw [Real.rpow_one],
          show (1:ℝ) = (1/3:ℝ)*3 by norm_num, Real.rpow_mul (le_of_lt ht)]
      exact Real.rpow_natCast _ 3
    have htwo : t^2 = u^6 := by rw [hthree]; ring
    rw [ht7, ht5, ht2, ht10, ht1, htwo]
    field_simp
  rw [key]
  set T1 := (t ^ ((5:ℝ)/3) * D3) * (t ^ ((2:ℝ)/3) / Real.sqrt I) / 2 with hT1def
  set T2 := (3/4) * ((D1 / t ^ ((1:ℝ)/3)) * (D2 * t ^ ((2:ℝ)/3)) * (t^2 / (Real.sqrt I)^3)) with hT2def
  set T3 := (3/8) * ((D1 / t ^ ((1:ℝ)/3))^3 * (t ^ ((10:ℝ)/3) / (Real.sqrt I)^5)) with hT3def
  have hT1 : |T1| ≤ b3 * b4 / 2 := by
    rw [hT1def, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    gcongr
  have hT2 : |T2| ≤ 3/4 * (b1 * b2 * b5) := by
    rw [hT2def, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4), abs_mul, abs_mul]
    gcongr
  have hT3 : |T3| ≤ 3/8 * (b1^3 * b6) := by
    rw [hT3def, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/8), abs_mul, abs_pow]
    gcongr
  have htri : |T1 - T2 + T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 - T2 + T3| ≤ |T1 - T2| + |T3| := abs_add_le _ _
    have h2 : |T1 - T2| ≤ |T1| + |T2| := by
      have := abs_add_le T1 (-T2)
      rwa [← sub_eq_add_neg, abs_neg] at this
    linarith
  exact le_trans htri (add_le_add (add_le_add hT1 hT2) hT3)

end Commons.Analysis.Calculus