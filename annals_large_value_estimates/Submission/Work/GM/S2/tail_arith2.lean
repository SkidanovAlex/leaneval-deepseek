import Mathlib

namespace Work.GM.S2

theorem tail_arith2 {A T η N : ℝ} {kk j : ℕ} (hA : A = 1 + (2 : ℝ) ^ (kk + 1))
    (hkkT : (2 : ℝ) ^ (kk + 1) ≤ 4 * T) (hT : 1 ≤ T) (hN : 0 < N)
    (hηj : 24 ≤ η * ((j : ℝ) - 1)) (hη : 0 < η) :
    A / (N * T ^ (η * ((j : ℝ) - 1))) ≤ 8 * T ^ (-(23 : ℝ)) / N := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hηpos : 0 < η := hη
  set X : ℝ := T ^ (η * ((j : ℝ) - 1)) with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]; exact Real.rpow_pos_of_pos hTpos _
  have hA8 : A ≤ 8 * T := by
    rw [hA]; linarith
  have hX24 : T ^ (24 : ℝ) ≤ X := by
    rw [hXdef]; exact Real.rpow_le_rpow_of_exponent_le hT hηj
  have hTneg : 0 < T ^ (-(23 : ℝ)) := Real.rpow_pos_of_pos hTpos _
  have hstep : T ≤ T ^ (-(23 : ℝ)) * X := by
    have h1 : T ^ (-(23 : ℝ)) * T ^ (24 : ℝ) ≤ T ^ (-(23 : ℝ)) * X :=
      mul_le_mul_of_nonneg_left hX24 (le_of_lt hTneg)
    have h2 : T ^ (-(23 : ℝ)) * T ^ (24 : ℝ) = T := by
      rw [← Real.rpow_add hTpos]
      have he : -(23 : ℝ) + 24 = 1 := by norm_num
      rw [he, Real.rpow_one]
    rwa [h2] at h1
  have hkey : A ≤ 8 * T ^ (-(23 : ℝ)) * X := by
    have h : 8 * T ≤ 8 * (T ^ (-(23 : ℝ)) * X) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 8)
    have h3 : 8 * (T ^ (-(23 : ℝ)) * X) = 8 * T ^ (-(23 : ℝ)) * X := by ring
    linarith
  calc A / (N * X) ≤ (8 * T ^ (-(23 : ℝ)) * X) / (N * X) :=
        div_le_div_of_nonneg_right hkey (le_of_lt (mul_pos hN hXpos))
    _ = 8 * T ^ (-(23 : ℝ)) / N := by
        rw [mul_div_mul_right _ _ (ne_of_gt hXpos)]

end Work.GM.S2
