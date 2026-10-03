import Mathlib

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

/-- Elementary arithmetic of the `lip-2` general tail: from the lower bound
`Y ≥ (2 Ct (CE (CA+1))² CA + 1) δ^{-(2 KA)/11}` on `Y` and `Bf = CE (CA+1) CA δ^{-KA}`
one deduces `Ct Y^{-11} (Bf Nd) ≤ (δ^{KA}/(CE (CA+1))) Nd / 2`. -/
theorem lip2GenTailArith {CA KA CE Ct Y Bf Nd δ : ℝ}
    (hCA : 0 < CA) (hKA : 0 < KA) (hCE : 0 < CE) (hCt : 0 < Ct)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hNd : 0 ≤ Nd)
    (hBf : Bf = CE * (CA + 1) * CA * δ⁻¹ ^ KA)
    (hY : (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) * δ⁻¹ ^ ((KA + KA) / 11) ≤ Y) :
    Ct * Y⁻¹ ^ 11 * (Bf * Nd) ≤ (δ ^ KA / (CE * (CA + 1))) * Nd / 2 := by
  have hBpos : 0 < CE * (CA + 1) := by positivity
  have hcpos : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hApos : 0 < 2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1 := by positivity
  have hYpos : 0 < Y := lt_of_lt_of_le (mul_pos hApos (Real.rpow_pos_of_pos hcpos _)) hY
  have hPpos : 0 < δ ^ KA := Real.rpow_pos_of_pos hδ0 KA
  -- `δ^{2 KA} = (δ^{KA})²`
  have hδ2 : δ ^ (2 * KA) = (δ ^ KA) ^ 2 := by
    have h : δ ^ (KA * 2) = (δ ^ KA) ^ (2 : ℝ) := Real.rpow_mul hδ0.le KA 2
    rw [show (2 : ℝ) * KA = KA * 2 by ring]
    simpa using h
  -- the key product inequality, equivalent to the `Nd`-free form of the goal
  have hkey : 2 * (CE * (CA + 1)) ^ 2 * CA * Ct ≤ (δ ^ KA) ^ 2 * Y ^ 11 := by
    have h1 : ((2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) * δ⁻¹ ^ ((KA + KA) / 11)) ^ 11
        ≤ Y ^ 11 := pow_le_pow_left₀ (by positivity) hY 11
    have he : (δ⁻¹ ^ ((KA + KA) / 11)) ^ 11 = ((δ ^ KA) ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast (δ⁻¹ ^ ((KA + KA) / 11)) 11,
        ← Real.rpow_mul (le_of_lt hcpos)]
      rw [show (KA + KA) / 11 * ((11 : ℕ) : ℝ) = 2 * KA by push_cast; ring]
      rw [Real.inv_rpow hδ0.le]
      exact congrArg (fun x : ℝ => x⁻¹) hδ2
    have h3 : (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) ^ 11 * ((δ ^ KA) ^ 2)⁻¹
        ≤ Y ^ 11 := by
      simpa only [mul_pow, he] using h1
    have h4 : (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) ^ 11 ≤ Y ^ 11 * (δ ^ KA) ^ 2 := by
      have hp : 0 < (δ ^ KA) ^ 2 := pow_pos hPpos 2
      have h3' : (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) ^ 11 / (δ ^ KA) ^ 2 ≤ Y ^ 11 := by
        simpa only [div_eq_mul_inv] using h3
      exact (div_le_iff₀ hp).mp h3'
    have hA1 : 1 ≤ 2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1 := by
      have hnn : 0 ≤ 2 * Ct * (CE * (CA + 1)) ^ 2 * CA := by positivity
      linarith
    have hA11 : 2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1
        ≤ (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) ^ 11 := by
      have h := pow_le_pow_right₀ hA1 (by norm_num : (1 : ℕ) ≤ 11)
      simpa using h
    have h5 : 2 * Ct * (CE * (CA + 1)) ^ 2 * CA < Y ^ 11 * (δ ^ KA) ^ 2 := by
      have h6 := le_trans hA11 h4
      linarith
    linarith
  -- the same inequality with `Nd ≥ 0`:
  have hunit : Ct * Y⁻¹ ^ 11 * (CE * (CA + 1) * CA * δ⁻¹ ^ KA)
      ≤ (δ ^ KA / (CE * (CA + 1))) / 2 := by
    rw [inv_pow, Real.inv_rpow hδ0.le KA]
    have e1 : (2 * (CE * (CA + 1)) ^ 2 * CA * Ct)
          / (2 * (CE * (CA + 1)) * (δ ^ KA) * Y ^ 11)
        = Ct * (Y ^ 11)⁻¹ * (CE * (CA + 1) * CA * (δ ^ KA)⁻¹) := by
      field_simp
    have e2 : ((δ ^ KA) ^ 2 * Y ^ 11) / (2 * (CE * (CA + 1)) * (δ ^ KA) * Y ^ 11)
        = (δ ^ KA / (CE * (CA + 1))) / 2 := by
      field_simp
    have hdiv := div_le_div_of_nonneg_right hkey
      (by positivity : (0 : ℝ) ≤ 2 * (CE * (CA + 1)) * (δ ^ KA) * Y ^ 11)
    rw [← e1, ← e2]
    exact hdiv
  have hassoc : Ct * Y⁻¹ ^ 11 * ((CE * (CA + 1) * CA * δ⁻¹ ^ KA) * Nd)
      = (Ct * Y⁻¹ ^ 11 * (CE * (CA + 1) * CA * δ⁻¹ ^ KA)) * Nd :=
    (mul_assoc _ _ _).symm
  rw [hBf, hassoc]
  rw [← div_mul_eq_mul_div]
  exact mul_le_mul_of_nonneg_right hunit hNd

end Work.KMTAreas.A4
