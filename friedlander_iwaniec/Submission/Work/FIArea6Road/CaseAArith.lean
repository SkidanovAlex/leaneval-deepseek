import Mathlib

set_option maxHeartbeats 4000000

namespace Work.FIArea6Road

/-- Elementary arithmetic inequality used in case A of area 6: the two `θ`- and `N^{3/4}`-terms
on the left are absorbed by the large constant times `C_z · R · N · (log N)^6` on the right.

The proof multiplies the two *lower* bounds on `C_z` and `R` together.  Writing `L = log N`,
`P = log (4N)`, the key ingredients are `P ≤ 2L` (so `P^3 ≤ 8L^3`, `P^2 ≤ 4L^2`), the sharp
upper bound `θ ≤ R/(256 L^3)`, the two Taylor lower bounds `exp (7L/8) ≥ 343 L^3 / 3072` and
`exp (L/8) ≥ L^3/3072`, and the simple relation `C_z · 4d · L^6 ≥ 1/2500`. -/
theorem CaseAArith (N θ d C₁ C_z R : ℝ)
    (hN1 : 1 ≤ N) (hlogN : 1000 ≤ Real.log N) (hd : 1 ≤ d) (hC₁ : 0 < C₁)
    (hCz : 1 / (10000 * d * (Real.log N) ^ (6 : ℕ)) ≤ C_z)
    (hθ : 0 ≤ θ) (hcase : θ ≤ R / (256 * (Real.log N) ^ (3 : ℕ)))
    (hR : Real.exp (-(Real.log N / 8)) ≤ R) :
    4 * (C₁ * (θ * N + 1) * (Real.log (4 * N)) ^ (3 : ℕ)
          + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * (Real.log (4 * N)) ^ (2 : ℕ))
      ≤ ((10 : ℝ) ^ 100 * (C₁ + 1)) * C_z * R * (4 * d) * N * (Real.log N) ^ (6 : ℕ) := by
  set L : ℝ := Real.log N with hLdef
  set P : ℝ := Real.log (4 * N) with hPdef
  -- basic positivity
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hLge : 1000 ≤ L := by rw [hLdef]; exact hlogN
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hL3nn : 0 ≤ L ^ 3 := pow_nonneg hLnn 3
  have hC1nn : 0 ≤ C₁ := le_of_lt hC₁
  have hC1pos : 0 < C₁ + 1 := by linarith
  have hC1nn' : 0 ≤ C₁ + 1 := le_of_lt hC1pos
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR
  have hRnn : 0 ≤ R := le_of_lt hRpos
  have hNRnn : 0 ≤ N * R := mul_nonneg (le_of_lt hNpos) hRnn
  -- converted hypotheses
  have hR' : Real.exp (-(L / 8)) ≤ R := by rw [hLdef]; exact hR
  have hcase' : θ ≤ R / (256 * L ^ (3 : ℕ)) := by rw [hLdef]; exact hcase
  have hCz' : 1 / (10000 * d * L ^ (6 : ℕ)) ≤ C_z := by rw [hLdef]; exact hCz
  have hexpL : Real.exp L = N := by rw [hLdef]; exact Real.exp_log hNpos
  -- `log 4 ≤ L`
  have hlog4_le : Real.log 4 ≤ L := by
    have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h4
    linarith
  -- `P ≤ 2L`, `0 ≤ P`
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    apply Real.log_nonneg
    nlinarith [hN1]
  have hPle : P ≤ 2 * L := by
    rw [hPdef, Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) (ne_of_gt hNpos)]
    linarith [hlog4_le, hLdef]
  have hP3 : P ^ 3 ≤ 8 * L ^ 3 := by
    have h := pow_le_pow_left₀ hPnn hPle 3
    have h8 : (2 * L) ^ 3 = 8 * L ^ 3 := by ring
    rwa [h8] at h
  have hP2 : P ^ 2 ≤ 4 * L ^ 2 := by
    have h := pow_le_pow_left₀ hPnn hPle 2
    have h4 : (2 * L) ^ 2 = 4 * L ^ 2 := by ring
    rwa [h4] at h
  -- Taylor lower bounds for the exponential
  have hexp8 : L ^ 3 / 3072 ≤ Real.exp (L / 8) := by
    have h := Real.pow_div_factorial_le_exp (L / 8) (by positivity) 3
    have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h3] at h
    have heq : (L / 8) ^ 3 / 6 = L ^ 3 / 3072 := by ring
    rwa [heq] at h
  have hexp7 : 343 * L ^ 3 / 3072 ≤ Real.exp (7 * L / 8) := by
    have h := Real.pow_div_factorial_le_exp (7 * L / 8) (by positivity) 3
    have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h3] at h
    have heq : (7 * L / 8) ^ 3 / 6 = 343 * L ^ 3 / 3072 := by ring
    rwa [heq] at h
  -- `exp (7L/8) ≤ N·R`
  have hNR7 : Real.exp (7 * L / 8) ≤ N * R := by
    have he : Real.exp (7 * L / 8) = Real.exp L * Real.exp (-(L / 8)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he, ← hexpL]
    exact mul_le_mul_of_nonneg_left hR' (le_of_lt (Real.exp_pos L))
  -- `L^2 ≤ 4 exp (L/8)`
  have hexp8' : L ^ 2 ≤ 4 * Real.exp (L / 8) := by
    have h := hexp8
    have hge : 1000 * L ^ 2 ≤ L ^ 3 := by nlinarith [hLge, sq_nonneg L]
    have hle : L ^ 3 ≤ Real.exp (L / 8) * 3072 := by
      rw [div_le_iff₀ (show (0 : ℝ) < 3072 by norm_num)] at h; exact h
    nlinarith [hge, hle, Real.exp_pos (L / 8)]
  -- `32 L^3 ≤ 10^96 · N · R`
  have hT2 : 32 * L ^ 3 ≤ (10 : ℝ) ^ 96 * N * R := by
    have hc : (32 : ℝ) ≤ (10 : ℝ) ^ 96 * (343 / 3072) := by norm_num
    have h1 : 32 * L ^ 3 ≤ (10 : ℝ) ^ 96 * (343 * L ^ 3 / 3072) := by
      rw [show (10 : ℝ) ^ 96 * (343 * L ^ 3 / 3072)
            = ((10 : ℝ) ^ 96 * (343 / 3072)) * L ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right hc hL3nn
    have h2 : (10 : ℝ) ^ 96 * (343 * L ^ 3 / 3072) ≤ (10 : ℝ) ^ 96 * Real.exp (7 * L / 8) :=
      mul_le_mul_of_nonneg_left hexp7 (by norm_num)
    have h3 : (10 : ℝ) ^ 96 * Real.exp (7 * L / 8) ≤ (10 : ℝ) ^ 96 * (N * R) :=
      mul_le_mul_of_nonneg_left hNR7 (by norm_num)
    calc 32 * L ^ 3 ≤ (10 : ℝ) ^ 96 * (343 * L ^ 3 / 3072) := h1
      _ ≤ (10 : ℝ) ^ 96 * Real.exp (7 * L / 8) := h2
      _ ≤ (10 : ℝ) ^ 96 * (N * R) := h3
      _ = (10 : ℝ) ^ 96 * N * R := by ring
  -- `2^(3/4) ≤ 2`, `N^(3/4) = exp (3L/4)`, `exp(3L/4)·exp(L/8)=exp(7L/8)`
  have h2pow : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show ((3 : ℝ) / 4) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hNpow : N ^ ((3 : ℝ) / 4) = Real.exp (3 * L / 4) := by
    rw [← hexpL, ← Real.exp_mul L ((3 : ℝ) / 4)]
    congr 1; ring
  have hexpmul : Real.exp (3 * L / 4) * Real.exp (L / 8) = Real.exp (7 * L / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  -- `16 · 2^(3/4) · N^(3/4) · L^2 ≤ 10^96 · N · R`
  have hT3 : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) * L ^ 2
      ≤ (10 : ℝ) ^ 96 * N * R := by
    have hstepA : (2 : ℝ) ^ ((3 : ℝ) / 4) * L ^ 2 ≤ 8 * Real.exp (L / 8) := by
      calc (2 : ℝ) ^ ((3 : ℝ) / 4) * L ^ 2 ≤ 2 * L ^ 2 :=
            mul_le_mul_of_nonneg_right h2pow (sq_nonneg L)
        _ ≤ 2 * (4 * Real.exp (L / 8)) := mul_le_mul_of_nonneg_left hexp8' (by norm_num)
        _ = 8 * Real.exp (L / 8) := by ring
    have hNpow_nn : 0 ≤ 16 * N ^ ((3 : ℝ) / 4) := by positivity
    calc 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) * L ^ 2
        = 16 * N ^ ((3 : ℝ) / 4) * ((2 : ℝ) ^ ((3 : ℝ) / 4) * L ^ 2) := by ring
      _ ≤ 16 * N ^ ((3 : ℝ) / 4) * (8 * Real.exp (L / 8)) :=
            mul_le_mul_of_nonneg_left hstepA hNpow_nn
      _ = 16 * Real.exp (3 * L / 4) * (8 * Real.exp (L / 8)) := by rw [hNpow]
      _ = 128 * (Real.exp (3 * L / 4) * Real.exp (L / 8)) := by ring
      _ = 128 * Real.exp (7 * L / 8) := by rw [hexpmul]
      _ ≤ 128 * (N * R) := mul_le_mul_of_nonneg_left hNR7 (by norm_num)
      _ ≤ (10 : ℝ) ^ 96 * (N * R) := mul_le_mul_of_nonneg_right (by norm_num) hNRnn
      _ = (10 : ℝ) ^ 96 * N * R := by ring
  -- `C_z · 4d · L^6 ≥ 1/2500`
  have hCzmul : (1 : ℝ) / 2500 ≤ C_z * (4 * d) * L ^ 6 := by
    have hpos : (0 : ℝ) < 10000 * d * L ^ 6 := by positivity
    have h := mul_le_mul_of_nonneg_right hCz' (le_of_lt hpos)
    have hsimp : (1 / (10000 * d * L ^ 6)) * (10000 * d * L ^ 6) = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
    rw [hsimp] at h
    have heq : C_z * (10000 * d * L ^ 6) = 2500 * (C_z * (4 * d) * L ^ 6) := by ring
    rw [heq] at h
    linarith
  -- lower bound on the right-hand side
  have hRHS_eq : ((10 : ℝ) ^ 100 * (C₁ + 1)) * C_z * R * (4 * d) * N * L ^ 6
      = (10 : ℝ) ^ 100 * (C₁ + 1) * R * N * (C_z * (4 * d) * L ^ 6) := by ring
  have hRHS_lower : 4 * ((10 : ℝ) ^ 96 * (C₁ + 1) * N * R)
      ≤ ((10 : ℝ) ^ 100 * (C₁ + 1)) * C_z * R * (4 * d) * N * L ^ 6 := by
    rw [hRHS_eq]
    have hconst : (10 : ℝ) ^ 100 * (1 / 2500) = 4 * (10 : ℝ) ^ 96 := by norm_num
    have step1 : 4 * ((10 : ℝ) ^ 96 * (C₁ + 1) * N * R)
        = (10 : ℝ) ^ 100 * (C₁ + 1) * R * N * (1 / 2500) := by
      rw [show 4 * ((10 : ℝ) ^ 96 * (C₁ + 1) * N * R)
            = ((10 : ℝ) ^ 100 * (1 / 2500)) * (C₁ + 1) * N * R by rw [hconst]; ring]
      ring
    rw [step1]
    exact mul_le_mul_of_nonneg_left hCzmul (by positivity)
  -- term bounds
  have hterm1 : C₁ * θ * N * P ^ 3 ≤ C₁ * N * R / 32 := by
    have htheta : θ * P ^ 3 ≤ R / 32 := by
      have h256 : 256 * L ^ 3 * θ ≤ R := by
        have hpos : (0 : ℝ) < 256 * L ^ 3 := by positivity
        calc 256 * L ^ 3 * θ ≤ 256 * L ^ 3 * (R / (256 * L ^ 3)) :=
              mul_le_mul_of_nonneg_left hcase' (le_of_lt hpos)
          _ = R := by rw [mul_div_cancel₀ R (ne_of_gt hpos)]
      have h1 : θ * P ^ 3 ≤ θ * (8 * L ^ 3) := mul_le_mul_of_nonneg_left hP3 hθ
      have h2 : θ * (8 * L ^ 3) ≤ R / 32 := by
        rw [show 256 * L ^ 3 * θ = (θ * (8 * L ^ 3)) * 32 by ring] at h256
        exact (le_div_iff₀ (show (0 : ℝ) < 32 by norm_num)).mpr h256
      linarith [h1, h2]
    have h := mul_le_mul_of_nonneg_left htheta (mul_nonneg hC1nn (le_of_lt hNpos))
    calc C₁ * θ * N * P ^ 3 = C₁ * N * (θ * P ^ 3) := by ring
      _ ≤ C₁ * N * (R / 32) := h
      _ = C₁ * N * R / 32 := by ring
  have hterm2 : C₁ * P ^ 3 ≤ 8 * C₁ * L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hP3 hC1nn
    calc C₁ * P ^ 3 ≤ C₁ * (8 * L ^ 3) := h
      _ = 8 * C₁ * L ^ 3 := by ring
  have hterm3 : C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2
      ≤ 4 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
    have hrpow : (2 * N) ^ ((3 : ℝ) / 4) = (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) (le_of_lt hNpos)
    rw [hrpow]
    have hnn : 0 ≤ C₁ * ((2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) := by positivity
    have h := mul_le_mul_of_nonneg_left hP2 hnn
    calc C₁ * ((2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) * P ^ 2
        ≤ C₁ * ((2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) * (4 * L ^ 2) := h
      _ = 4 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2 := by ring
  -- assembly
  have hbound1 : 4 * (C₁ * (θ * N + 1) * P ^ 3 + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2)
      ≤ C₁ * N * R / 8 + 32 * C₁ * L ^ 3
          + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
    have hexpand : 4 * (C₁ * (θ * N + 1) * P ^ 3 + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2)
        = 4 * (C₁ * θ * N * P ^ 3 + C₁ * P ^ 3
              + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2) := by ring
    rw [hexpand]
    have hsum := add_le_add (add_le_add hterm1 hterm2) hterm3
    have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * (C₁ * θ * N * P ^ 3 + C₁ * P ^ 3
            + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2)
        ≤ 4 * (C₁ * N * R / 32 + 8 * C₁ * L ^ 3
              + 4 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2) := hmul
      _ = C₁ * N * R / 8 + 32 * C₁ * L ^ 3
            + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2 := by ring
  have hbound2 : C₁ * N * R / 8 + 32 * C₁ * L ^ 3
        + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2
      ≤ (C₁ + 1) * N * R / 8 + 32 * (C₁ + 1) * L ^ 3
        + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
    have h1 : C₁ * N * R / 8 ≤ (C₁ + 1) * N * R / 8 := by
      have hNR : C₁ * (N * R) ≤ (C₁ + 1) * (N * R) :=
        mul_le_mul_of_nonneg_right (by linarith) hNRnn
      nlinarith [hNR]
    have h2 : 32 * C₁ * L ^ 3 ≤ 32 * (C₁ + 1) * L ^ 3 := by
      have hL : C₁ * L ^ 3 ≤ (C₁ + 1) * L ^ 3 := mul_le_mul_of_nonneg_right (by linarith) hL3nn
      linarith
    have h3 : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2
        ≤ 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
      have hNL : C₁ * (N ^ ((3 : ℝ) / 4) * L ^ 2) ≤ (C₁ + 1) * (N ^ ((3 : ℝ) / 4) * L ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have ha : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2
          = (16 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * (C₁ * (N ^ ((3 : ℝ) / 4) * L ^ 2)) := by ring
      have hb : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2
          = (16 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * ((C₁ + 1) * (N ^ ((3 : ℝ) / 4) * L ^ 2)) := by
        ring
      rw [ha, hb]
      exact mul_le_mul_of_nonneg_left hNL (by positivity)
    linarith [h1, h2, h3]
  have hbound3 : (C₁ + 1) * N * R / 8 + 32 * (C₁ + 1) * L ^ 3
        + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2
      ≤ 3 * ((C₁ + 1) * ((10 : ℝ) ^ 96 * N * R)) := by
    have he1 : (C₁ + 1) * N * R / 8 ≤ (C₁ + 1) * ((10 : ℝ) ^ 96 * N * R) := by
      have hK : 0 ≤ (C₁ + 1) * N * R := by positivity
      have hstep := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 8 ≤ (10 : ℝ) ^ 96 by norm_num) hK
      have ha : (C₁ + 1) * N * R / 8 = (1 / 8) * ((C₁ + 1) * N * R) := by ring
      have hb : (C₁ + 1) * ((10 : ℝ) ^ 96 * N * R) = (10 : ℝ) ^ 96 * ((C₁ + 1) * N * R) := by ring
      rw [ha, hb]; exact hstep
    have he2 : 32 * (C₁ + 1) * L ^ 3 ≤ (C₁ + 1) * ((10 : ℝ) ^ 96 * N * R) := by
      have hstep := mul_le_mul_of_nonneg_left hT2 hC1nn'
      have ha : 32 * (C₁ + 1) * L ^ 3 = (C₁ + 1) * (32 * L ^ 3) := by ring
      rw [ha]; exact hstep
    have he3 : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2
        ≤ (C₁ + 1) * ((10 : ℝ) ^ 96 * N * R) := by
      have hstep := mul_le_mul_of_nonneg_left hT3 hC1nn'
      have ha : 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2
          = (C₁ + 1) * (16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) * L ^ 2) := by ring
      rw [ha]; exact hstep
    linarith [he1, he2, he3]
  calc 4 * (C₁ * (θ * N + 1) * P ^ 3 + C₁ * (2 * N) ^ ((3 : ℝ) / 4) * P ^ 2)
      ≤ C₁ * N * R / 8 + 32 * C₁ * L ^ 3
          + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * C₁ * N ^ ((3 : ℝ) / 4) * L ^ 2 := hbound1
    _ ≤ (C₁ + 1) * N * R / 8 + 32 * (C₁ + 1) * L ^ 3
          + 16 * (2 : ℝ) ^ ((3 : ℝ) / 4) * (C₁ + 1) * N ^ ((3 : ℝ) / 4) * L ^ 2 := hbound2
    _ ≤ 3 * ((C₁ + 1) * ((10 : ℝ) ^ 96 * N * R)) := hbound3
    _ = 3 * ((10 : ℝ) ^ 96 * (C₁ + 1) * N * R) := by ring
    _ ≤ 4 * ((10 : ℝ) ^ 96 * (C₁ + 1) * N * R) := by
          have hnn : (0 : ℝ) ≤ (10 : ℝ) ^ 96 * (C₁ + 1) * N * R := by positivity
          nlinarith [hnn]
    _ ≤ ((10 : ℝ) ^ 100 * (C₁ + 1)) * C_z * R * (4 * d) * N * L ^ 6 := hRHS_lower

end Work.FIArea6Road
