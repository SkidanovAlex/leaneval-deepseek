import Mathlib

namespace Work.FIArea3

/-- **Product bound for `√K₁·K₂`.** With `K₁ ≤ 2(2N)^{1/4}`, `K₂ ≤ 2(4πθN)^{1/4}`, `1 ≤ K₁,K₂`,
`1 ≤ N`, `0 < θ ≤ 1`: `√K₁·K₂ ≤ 8·N^{3/8}`. -/
theorem sqrtK1_K2_le (N θ K1 K2 : ℝ) (hN : 1 ≤ N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hK1 : 1 ≤ K1) (hK1ub : K1 ≤ 2 * (2 * N) ^ ((1 : ℝ) / 4))
    (hK2 : 1 ≤ K2) (hK2ub : K2 ≤ 2 * (4 * Real.pi * θ * N) ^ ((1 : ℝ) / 4)) :
    Real.sqrt K1 * K2 ≤ 8 * N ^ ((3 : ℝ) / 8) := by
  have hNpos : 0 < N := by linarith
  have hNnn : 0 ≤ N := le_of_lt hNpos
  have hK1nn : 0 ≤ K1 := by linarith
  have hK2nn : 0 ≤ K2 := by linarith
  have h2Nnn : 0 ≤ 2 * N := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Step 1: bound √K₁ by √2 · 2^{1/8} · N^{1/8}.
  have hstep1 : K1 ^ ((1 : ℝ) / 2) ≤ (2 * (2 * N) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hK1nn hK1ub (by norm_num)
  have hstep2 : (2 * (2 * N) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2)
      = 2 ^ ((1 : ℝ) / 2) * ((2 * N) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) :=
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg h2Nnn _)
  have hstep3 : ((2 * N) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) = (2 * N) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_mul h2Nnn]
    norm_num
  have hA : Real.sqrt K1 ≤ (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow K1]
    calc K1 ^ ((1 : ℝ) / 2)
        ≤ (2 * (2 * N) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) := hstep1
      _ = 2 ^ ((1 : ℝ) / 2) * (2 * N) ^ ((1 : ℝ) / 8) := by rw [hstep2, hstep3]
      _ = (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8) := by
            rw [Real.sqrt_eq_rpow 2, Real.mul_rpow (by norm_num) hNnn]
            ring
  -- The numerical constant √2 · 2^{1/8} ≤ 2.
  have hXY : Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8) ≤ 2 := by
    calc Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)
        = 2 ^ ((1 : ℝ) / 2) * 2 ^ ((1 : ℝ) / 8) := by rw [Real.sqrt_eq_rpow]
      _ = 2 ^ ((1 : ℝ) / 2 + (1 : ℝ) / 8) := (Real.rpow_add h2pos _ _).symm
      _ ≤ 2 ^ 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  -- The bound (4πθ)^{1/4} ≤ 2.
  have h4pin : 0 ≤ 4 * Real.pi * θ := by positivity
  have h4pile : 4 * Real.pi * θ ≤ 16 := by
    nlinarith [Real.pi_le_four, Real.pi_pos, hθ, hθ1]
  have h4pi : (4 * Real.pi * θ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    have h2pow : (16 : ℝ) = (2 : ℝ) ^ ((4 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
    have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [h2pow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
    calc (4 * Real.pi * θ) ^ ((1 : ℝ) / 4) ≤ (16 : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow h4pin h4pile (by norm_num)
      _ = 2 := h16
  -- Step 2: bound K₂ by 4 · N^{1/4}.
  have hB : K2 ≤ 4 * N ^ ((1 : ℝ) / 4) := by
    have hN14nn : 0 ≤ N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hNnn _
    calc K2 ≤ 2 * (4 * Real.pi * θ * N) ^ ((1 : ℝ) / 4) := hK2ub
      _ = 2 * ((4 * Real.pi * θ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4)) := by
            rw [Real.mul_rpow h4pin hNnn]
      _ = 2 * (4 * Real.pi * θ) ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) := by ring
      _ ≤ 4 * N ^ ((1 : ℝ) / 4) := by
            apply mul_le_mul_of_nonneg_right _ hN14nn
            linarith [h4pi]
  -- Step 3: multiply and collect powers of N.
  have hbnn : 0 ≤ (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8) := by positivity
  have hprod : Real.sqrt K1 * K2
      ≤ ((Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8)) * (4 * N ^ ((1 : ℝ) / 4)) :=
    mul_le_mul hA hB hK2nn hbnn
  have hN38nn : 0 ≤ N ^ ((3 : ℝ) / 8) := Real.rpow_nonneg hNnn _
  have hrw : N ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 4) = N ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have h4XY : 4 * (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) ≤ 8 := by linarith [hXY]
  have hfinal : ((Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8)) * (4 * N ^ ((1 : ℝ) / 4))
      ≤ 8 * N ^ ((3 : ℝ) / 8) := by
    calc ((Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8)) * N ^ ((1 : ℝ) / 8)) * (4 * N ^ ((1 : ℝ) / 4))
        = (4 * (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8))) * (N ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 4)) := by
          ring
      _ = (4 * (Real.sqrt 2 * 2 ^ ((1 : ℝ) / 8))) * N ^ ((3 : ℝ) / 8) := by rw [hrw]
      _ ≤ 8 * N ^ ((3 : ℝ) / 8) := mul_le_mul_of_nonneg_right h4XY hN38nn
  exact le_trans hprod hfinal

end Work.FIArea3
