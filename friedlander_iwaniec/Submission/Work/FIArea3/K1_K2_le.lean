import Mathlib

namespace Work.FIArea3

/-- For `b ≥ 0`, `(b ^ 4) ^ (1/4) = b`. -/
private lemma rpow_four_quarter (b : ℝ) (hb : 0 ≤ b) : (b ^ 4) ^ ((1 : ℝ) / 4) = b := by
  rw [← Real.rpow_natCast_mul hb 4 ((1 : ℝ) / 4)]
  rw [show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]

/-- `16 ^ (1/4) = 2`. -/
private lemma sixteen_rpow_quarter : ((16 : ℝ)) ^ ((1 : ℝ) / 4) = 2 := by
  have h : ((2 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = 2 := rpow_four_quarter 2 (by norm_num)
  rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num]
  exact h

/-- **Product bound for `K₁·K₂`.** With `K₁ ≤ 2(2N)^{1/4}`, `K₂ ≤ 2(4πθN)^{1/4}`, `1 ≤ K₁,K₂`,
`1 ≤ N`, `0 < θ ≤ 1`: `K₁·K₂ ≤ 16·N^{1/2}`. -/
theorem K1_K2_le (N θ K1 K2 : ℝ) (hN : 1 ≤ N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hK1 : 1 ≤ K1) (hK1ub : K1 ≤ 2 * (2 * N) ^ ((1 : ℝ) / 4))
    (hK2 : 1 ≤ K2) (hK2ub : K2 ≤ 2 * (4 * Real.pi * θ * N) ^ ((1 : ℝ) / 4)) :
    K1 * K2 ≤ 16 * N ^ ((1 : ℝ) / 2) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hNnn : (0 : ℝ) ≤ N := hNpos.le
  -- π·θ ≤ 4 since π < 4 and θ ≤ 1
  have hpiθ : Real.pi * θ ≤ 4 := by
    have h1 : Real.pi * θ ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hθ1 Real.pi_pos.le
    linarith [Real.pi_lt_four]
  -- 2^{1/4} ≤ 2
  have h2q : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 : ℝ) / 4 ≤ 1 by norm_num)
    simpa using this
  -- 16^{1/4} = 2
  have h16q : ((16 : ℝ)) ^ ((1 : ℝ) / 4) = 2 := sixteen_rpow_quarter
  -- K₁ ≤ 4 N^{1/4}
  have hK1b : K1 ≤ 4 * N ^ ((1 : ℝ) / 4) := by
    refine le_trans hK1ub ?_
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNnn]
    have hNq : (0 : ℝ) ≤ N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hNnn _
    have hA : (2 : ℝ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) ≤ 2 * N ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h2q hNq
    have hB : 2 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4))
        ≤ 2 * (2 * N ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    linarith
  -- K₂ ≤ 4 N^{1/4}
  have hK2b : K2 ≤ 4 * N ^ ((1 : ℝ) / 4) := by
    refine le_trans hK2ub ?_
    have h4nn : (0 : ℝ) ≤ 4 * Real.pi * θ := by positivity
    rw [Real.mul_rpow h4nn hNnn]
    have h4q : (4 * Real.pi * θ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      have h16 : (4 * Real.pi * θ) ≤ 16 := by linarith
      have h := Real.rpow_le_rpow h4nn h16 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
      rwa [h16q] at h
    have hNq : (0 : ℝ) ≤ N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hNnn _
    have hA : (4 * Real.pi * θ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) ≤ 2 * N ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h4q hNq
    have hB : 2 * ((4 * Real.pi * θ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4))
        ≤ 2 * (2 * N ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    linarith
  have hK2nn : (0 : ℝ) ≤ K2 := le_trans zero_le_one hK2
  have h4Nnn : (0 : ℝ) ≤ 4 * N ^ ((1 : ℝ) / 4) := by positivity
  have hprod : K1 * K2 ≤ (4 * N ^ ((1 : ℝ) / 4)) * (4 * N ^ ((1 : ℝ) / 4)) :=
    mul_le_mul hK1b hK2b hK2nn h4Nnn
  have hsq : N ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) = N ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hNpos, show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num]
  calc K1 * K2 ≤ (4 * N ^ ((1 : ℝ) / 4)) * (4 * N ^ ((1 : ℝ) / 4)) := hprod
    _ = 16 * N ^ ((1 : ℝ) / 2) := by
        rw [show (4 * N ^ ((1 : ℝ) / 4)) * (4 * N ^ ((1 : ℝ) / 4))
              = 16 * (N ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4)) by ring, hsq]

end Work.FIArea3
