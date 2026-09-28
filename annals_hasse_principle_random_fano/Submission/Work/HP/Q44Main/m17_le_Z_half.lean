import Mathlib

namespace Work.HP.Q44Main

/-- From `M^106 * Δ ≤ Z^3` with `M, Z, Δ ≥ 1` deduce `M^17 ≤ Z^(1/2)`.

Since `Δ ≥ 1` we get `M^106 ≤ Z^3`, hence `M ≤ Z^(3/106)`, and then
`M^17 ≤ Z^(3·17/106) = Z^(51/106) ≤ Z^(1/2)`. -/
theorem m17_le_Z_half (M Z Δ : ℝ) (hM : 1 ≤ M) (hZ : 1 ≤ Z) (hΔ : 1 ≤ Δ)
    (hZ3 : M^(106:ℝ) * Δ ≤ Z^(3:ℝ)) :
    M^(17:ℝ) ≤ Z^((1:ℝ)/2) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hA : 0 < M ^ (106:ℝ) := Real.rpow_pos_of_pos hMpos 106
  -- Step 1: `Δ ≥ 1` removes `Δ` from the hypothesis.
  have hle : M ^ (106:ℝ) ≤ Z ^ (3:ℝ) := by
    calc M ^ (106:ℝ) = M ^ (106:ℝ) * 1 := (mul_one _).symm
      _ ≤ M ^ (106:ℝ) * Δ := mul_le_mul_of_nonneg_left hΔ (le_of_lt hA)
      _ ≤ Z ^ (3:ℝ) := hZ3
  -- Step 2: take the `1/106`-th powers.
  have hstep : (M ^ (106:ℝ)) ^ ((1:ℝ)/106) ≤ (Z ^ (3:ℝ)) ^ ((1:ℝ)/106) :=
    Real.rpow_le_rpow (le_of_lt hA) hle (by norm_num)
  have hM106 : (M ^ (106:ℝ)) ^ ((1:ℝ)/106) = M := by
    rw [← Real.rpow_mul hM0 106 (1/106),
      show (106:ℝ) * ((1:ℝ)/106) = 1 by norm_num, Real.rpow_one]
  have hZ3' : (Z ^ (3:ℝ)) ^ ((1:ℝ)/106) = Z ^ ((3:ℝ)/106) := by
    rw [← Real.rpow_mul hZ0 3 (1/106),
      show (3:ℝ) * ((1:ℝ)/106) = (3:ℝ)/106 by norm_num]
  have hMle : M ≤ Z ^ ((3:ℝ)/106) := by rw [hM106, hZ3'] at hstep; exact hstep
  -- Step 3: raise to the `17`-th power and compare exponents.
  calc M ^ (17:ℝ) ≤ (Z ^ ((3:ℝ)/106)) ^ (17:ℝ) :=
        Real.rpow_le_rpow hM0 hMle (by norm_num)
    _ = Z ^ (((3:ℝ)/106) * (17:ℝ)) := (Real.rpow_mul hZ0 (3/106) 17).symm
    _ ≤ Z ^ ((1:ℝ)/2) := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        norm_num

end Work.HP.Q44Main
