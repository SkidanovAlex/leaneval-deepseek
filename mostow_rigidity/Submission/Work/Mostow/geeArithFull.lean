import Mathlib

namespace Work.Mostow

/-- Elementary exponential/`rpow` arithmetic behind the tube lower bound: with
`ρ = arsinh (η₁/(2θ)) - 1`, `0 < θ ≤ 1` and `1 + m/2 ≤ N`, the lattice point count
`v * c₁ * exp(-N) * η₁^N/(Cn*CK) * θ^{-1}` is dominated by the tube volume
`v * c₁ * exp(N*ρ) / (Cn * (CK * θ^{-m/2}))`.

Mathematical content: after cancelling the positive factors `v, c₁, Cn, CK` and the
common `exp(-N)`, the claim is `η₁^N * θ^{-1} ≤ exp(N * arsinh(η₁/(2θ))) * θ^{m/2}`.
Since `θ^{m/2+1} ≥ θ^N` (`θ ≤ 1`, `m/2 + 1 ≤ N`) it suffices to prove
`η₁ ≤ exp(arsinh(η₁/(2θ))) * θ` and raise to the `N`-th power. -/
theorem geeArithFull (N m : ℕ) (v c₁ η₁ Cn CK θ ρ : ℝ)
    (hv : 0 < v) (hc₁ : 0 < c₁) (hη : 0 < η₁) (hCn : 0 < Cn) (hCK : 0 < CK)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hN : 1 + (m : ℝ) / 2 ≤ (N : ℝ))
    (hρ : ρ = Real.arsinh (η₁ / (2 * θ)) - 1) :
    (v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK)) * θ ^ (-1 : ℝ)
      ≤ (v * (c₁ * Real.exp ((N : ℝ) * ρ))) / (Cn * (CK * θ ^ (-(m : ℝ) / 2))) := by
  set y : ℝ := η₁ / (2 * θ) with hy_def
  have hy : 0 < y := by rw [hy_def]; positivity
  -- `η₁/(2θ) ≤ √(1 + (η₁/(2θ))^2)`
  have hsqrt : y ≤ Real.sqrt (1 + y ^ 2) := by
    refine (Real.le_sqrt (le_of_lt hy) (by positivity)).mpr ?_
    nlinarith [sq_nonneg y]
  -- Step 1: `η₁ ≤ exp (arsinh y) * θ`
  have hbase : η₁ ≤ Real.exp (Real.arsinh y) * θ := by
    rw [Real.exp_arsinh]
    have h2 : y * θ = η₁ / 2 := by rw [hy_def]; field_simp
    have h4 : θ * y = η₁ / 2 := by rw [mul_comm θ y, h2]
    have h3 : θ * y ≤ θ * Real.sqrt (1 + y ^ 2) :=
      mul_le_mul_of_nonneg_left hsqrt (le_of_lt hθ0)
    rw [add_mul, h2]
    linarith
  -- Step 2: raise to the `N`-th power
  have hpow : η₁ ^ N ≤ Real.exp ((N : ℝ) * Real.arsinh y) * θ ^ N := by
    rw [Real.exp_nat_mul]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (le_of_lt hη) hbase N
  -- Step 3: `θ^N ≤ θ^(m/2+1)` because `θ ≤ 1` and `N ≥ m/2 + 1`
  have hexp : θ ^ N ≤ θ ^ ((m : ℝ) / 2 + 1) := by
    have h := Real.rpow_le_rpow_of_exponent_ge (x := θ) (y := (N : ℝ)) (z := (m : ℝ) / 2 + 1)
      hθ0 hθ1 (by linarith)
    rwa [Real.rpow_natCast] at h
  have hcore₁ : η₁ ^ N ≤ Real.exp ((N : ℝ) * Real.arsinh y) * θ ^ ((m : ℝ) / 2 + 1) :=
    le_trans hpow (mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.exp_pos _)))
  -- Step 4: split `θ^(m/2+1) = θ^(m/2) * θ` and divide by `θ`
  have hcore'' : η₁ ^ N ≤ Real.exp ((N : ℝ) * Real.arsinh y) * θ ^ ((m : ℝ) / 2) * θ := by
    refine le_trans hcore₁ ?_
    rw [Real.rpow_add hθ0, Real.rpow_one, ← mul_assoc]
  have hcore : η₁ ^ N * θ ^ (-1 : ℝ) ≤ Real.exp ((N : ℝ) * Real.arsinh y) * θ ^ ((m : ℝ) / 2) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    exact (div_le_iff₀ hθ0).mpr hcore''
  -- Step 5: rewrite `exp (N*ρ)` using the definition of `ρ`
  have hρ' : Real.exp ((N : ℝ) * ρ)
      = Real.exp (-(N : ℝ)) * Real.exp ((N : ℝ) * Real.arsinh y) := by
    rw [hρ, hy_def]
    rw [show (N : ℝ) * (Real.arsinh (η₁ / (2 * θ)) - 1)
          = -(N : ℝ) + (N : ℝ) * Real.arsinh (η₁ / (2 * θ)) by ring]
    rw [Real.exp_add]
  have hK' : Real.exp (-(N : ℝ)) * η₁ ^ N * θ ^ (-1 : ℝ)
      ≤ Real.exp ((N : ℝ) * ρ) * θ ^ ((m : ℝ) / 2) := by
    have key : Real.exp ((N : ℝ) * ρ) * θ ^ ((m : ℝ) / 2)
        = Real.exp (-(N : ℝ)) * (Real.exp ((N : ℝ) * Real.arsinh y) * θ ^ ((m : ℝ) / 2)) := by
      rw [hρ', mul_assoc]
    have h1 : Real.exp (-(N : ℝ)) * η₁ ^ N * θ ^ (-1 : ℝ)
        = Real.exp (-(N : ℝ)) * (η₁ ^ N * θ ^ (-1 : ℝ)) := by
      rw [Real.rpow_neg_one]; ring
    rw [key, h1]
    exact mul_le_mul_of_nonneg_left hcore (le_of_lt (Real.exp_pos _))
  -- Step 6: multiply by `v * c₁ / (Cn * CK) > 0` and match the two sides
  have hpos : (0 : ℝ) < v * c₁ / (Cn * CK) := by positivity
  rw [show (-(m : ℝ)) / 2 = -((m : ℝ) / 2) by ring]
  have eq1 : (v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK)) * θ ^ (-1 : ℝ)
      = (v * c₁ / (Cn * CK)) * (Real.exp (-(N : ℝ)) * η₁ ^ N * θ ^ (-1 : ℝ)) := by
    rw [Real.rpow_neg_one]; ring
  have hrw : θ ^ ((m : ℝ) / 2) = (θ ^ (-((m : ℝ) / 2)))⁻¹ := by
    rw [Real.rpow_neg hθ0.le, inv_inv]
  have eq2 : v * (c₁ * Real.exp ((N : ℝ) * ρ)) / (Cn * (CK * θ ^ (-((m : ℝ) / 2))))
      = (v * c₁ / (Cn * CK)) * (Real.exp ((N : ℝ) * ρ) * θ ^ ((m : ℝ) / 2)) := by
    rw [hrw]; ring
  have hkey := mul_le_mul_of_nonneg_left hK' (le_of_lt hpos)
  rw [eq1, eq2]
  exact hkey

end Work.Mostow
