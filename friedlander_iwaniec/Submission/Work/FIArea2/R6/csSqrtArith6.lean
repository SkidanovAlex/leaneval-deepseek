import Mathlib

namespace Work.FIArea2.R6

theorem csSqrtArith6 {C2 C3 u N L : ℝ} (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hu1 : (1 : ℝ) / 10 ≤ u) (hu2 : u < N ^ ((3 : ℝ) / 8)) (hN : 1 ≤ N) (hL : 1 ≤ L) :
    C3 * (u ^ (2 : ℕ) + u + 1) * N ^ ((1 : ℝ) / 16)
        * Real.sqrt (C2 * (u ^ (2 : ℕ) + u + 1) * u * Real.sqrt N * (L + 2) ^ (16 : ℕ))
      ≤ C3 * Real.sqrt C2 * (111 : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (8 : ℕ)
          * (u ^ (3 : ℕ) * Real.sqrt N * L ^ ((2 : ℕ) ^ (19 : ℕ))) := by
  have hu : 0 ≤ u := by linarith
  have hN0 : 0 < N := by linarith
  have hA : 0 ≤ u ^ (2 : ℕ) + u + 1 := by positivity
  -- Expand the square root as a product of square roots.
  have hsqrt : Real.sqrt (C2 * (u ^ (2 : ℕ) + u + 1) * u * Real.sqrt N * (L + 2) ^ (16 : ℕ))
      = Real.sqrt C2 * Real.sqrt (u ^ (2 : ℕ) + u + 1) * Real.sqrt u
          * Real.sqrt (Real.sqrt N) * (L + 2) ^ (8 : ℕ) := by
    rw [show C2 * (u ^ (2 : ℕ) + u + 1) * u * Real.sqrt N * (L + 2) ^ (16 : ℕ)
         = C2 * ((u ^ (2 : ℕ) + u + 1) * (u * (Real.sqrt N * (L + 2) ^ (16 : ℕ)))) by ring]
    rw [Real.sqrt_mul hC2]
    rw [Real.sqrt_mul hA]
    rw [Real.sqrt_mul hu]
    rw [Real.sqrt_mul (Real.sqrt_nonneg N)]
    rw [show Real.sqrt ((L + 2) ^ (16 : ℕ)) = (L + 2) ^ (8 : ℕ) from by
          rw [show (L + 2) ^ (16 : ℕ) = ((L + 2) ^ (8 : ℕ)) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)]
    ring
  -- Bound the `u`-part: (u^2+u+1) * sqrt(u^2+u+1) ≤ 111^(3/2) u^3.
  have hAB : (u ^ (2 : ℕ) + u + 1) * Real.sqrt (u ^ (2 : ℕ) + u + 1)
      ≤ (111 : ℝ) ^ ((3 : ℝ) / 2) * u ^ (3 : ℕ) := by
    have hAle : u ^ 2 + u + 1 ≤ 111 * u ^ 2 := by nlinarith
    have hsA : Real.sqrt (u ^ 2 + u + 1) ≤ Real.sqrt 111 * u := by
      calc Real.sqrt (u ^ 2 + u + 1) ≤ Real.sqrt (111 * u ^ 2) := Real.sqrt_le_sqrt hAle
        _ = Real.sqrt 111 * u := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 111), Real.sqrt_sq hu]
    have hrt : (111 : ℝ) * Real.sqrt 111 = (111 : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 111), Real.rpow_one]
    calc (u ^ 2 + u + 1) * Real.sqrt (u ^ 2 + u + 1)
        ≤ (111 * u ^ 2) * (Real.sqrt 111 * u) :=
            mul_le_mul hAle hsA (Real.sqrt_nonneg _) (by positivity)
      _ = 111 * Real.sqrt 111 * u ^ 3 := by ring
      _ = (111 : ℝ) ^ ((3 : ℝ) / 2) * u ^ 3 := by rw [hrt]
  -- Bound the `N`-part: sqrt u * N^(1/16) * sqrt(sqrt N) ≤ sqrt N.
  have hNbl : Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N) ≤ Real.sqrt N := by
    have hsu : Real.sqrt u ≤ N ^ ((3 : ℝ) / 16) := by
      have h1 : Real.sqrt u ≤ Real.sqrt (N ^ ((3 : ℝ) / 8)) := Real.sqrt_le_sqrt (le_of_lt hu2)
      have h2 : Real.sqrt (N ^ ((3 : ℝ) / 8)) = N ^ ((3 : ℝ) / 16) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ N)]
        norm_num
      calc Real.sqrt u ≤ Real.sqrt (N ^ ((3 : ℝ) / 8)) := h1
        _ = N ^ ((3 : ℝ) / 16) := h2
    have hmerge : N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N) = N ^ ((5 : ℝ) / 16) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ N)]
      rw [← Real.rpow_add hN0]
      norm_num
    have hprod : N ^ ((3 : ℝ) / 16) * N ^ ((5 : ℝ) / 16) = N ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hN0]
      norm_num
    calc Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N)
        = Real.sqrt u * (N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N)) := by ring
      _ = Real.sqrt u * N ^ ((5 : ℝ) / 16) := by rw [hmerge]
      _ ≤ N ^ ((3 : ℝ) / 16) * N ^ ((5 : ℝ) / 16) :=
            mul_le_mul_of_nonneg_right hsu (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) _)
      _ = N ^ ((1 : ℝ) / 2) := hprod
      _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]
  -- Bound the `L`-part: (L+2)^8 ≤ 3^8 * L^(2^19).
  have hL8 : (L + 2) ^ (8 : ℕ) ≤ (3 : ℝ) ^ (8 : ℕ) * L ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    have h1 : L + 2 ≤ 3 * L := by linarith
    have h2 : (L + 2) ^ (8 : ℕ) ≤ (3 * L) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ L + 2) h1 8
    have h3 : (3 * L) ^ (8 : ℕ) = 3 ^ (8 : ℕ) * L ^ (8 : ℕ) := by rw [mul_pow]
    have h4 : L ^ (8 : ℕ) ≤ L ^ ((2 : ℕ) ^ (19 : ℕ)) := pow_le_pow_right₀ hL (by norm_num)
    calc (L + 2) ^ (8 : ℕ) ≤ (3 * L) ^ (8 : ℕ) := h2
      _ = 3 ^ (8 : ℕ) * L ^ (8 : ℕ) := h3
      _ ≤ 3 ^ (8 : ℕ) * L ^ ((2 : ℕ) ^ (19 : ℕ)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
  -- Combine the three bounds.
  have hcore : (u ^ 2 + u + 1) * Real.sqrt (u ^ 2 + u + 1)
        * (Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N)) * (L + 2) ^ (8 : ℕ)
      ≤ (111 : ℝ) ^ ((3 : ℝ) / 2) * u ^ (3 : ℕ) * Real.sqrt N
          * ((3 : ℝ) ^ (8 : ℕ) * L ^ ((2 : ℕ) ^ (19 : ℕ))) := by
    have h2n : 0 ≤ Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N) := by positivity
    have h3n : 0 ≤ (L + 2) ^ (8 : ℕ) := by positivity
    have h12 : (u ^ 2 + u + 1) * Real.sqrt (u ^ 2 + u + 1)
          * (Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N))
        ≤ (111 : ℝ) ^ ((3 : ℝ) / 2) * u ^ (3 : ℕ) * Real.sqrt N :=
      mul_le_mul hAB hNbl h2n (by positivity)
    exact mul_le_mul h12 hL8 h3n (by positivity)
  rw [hsqrt]
  have hrw1 : C3 * (u ^ 2 + u + 1) * N ^ ((1 : ℝ) / 16)
        * (Real.sqrt C2 * Real.sqrt (u ^ 2 + u + 1) * Real.sqrt u * Real.sqrt (Real.sqrt N)
            * (L + 2) ^ (8 : ℕ))
      = C3 * Real.sqrt C2 * ((u ^ 2 + u + 1) * Real.sqrt (u ^ 2 + u + 1)
          * (Real.sqrt u * N ^ ((1 : ℝ) / 16) * Real.sqrt (Real.sqrt N)) * (L + 2) ^ (8 : ℕ)) := by
    ring
  rw [hrw1]
  have hrw2 : C3 * Real.sqrt C2 * (111 : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (8 : ℕ)
        * (u ^ (3 : ℕ) * Real.sqrt N * L ^ ((2 : ℕ) ^ (19 : ℕ)))
      = C3 * Real.sqrt C2 * ((111 : ℝ) ^ ((3 : ℝ) / 2) * u ^ (3 : ℕ) * Real.sqrt N
          * ((3 : ℝ) ^ (8 : ℕ) * L ^ ((2 : ℕ) ^ (19 : ℕ)))) := by
    ring
  rw [hrw2]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

end Work.FIArea2.R6
