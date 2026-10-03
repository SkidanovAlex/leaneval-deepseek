/-
# `Submission.Work.FIArea7.nc_termL`

The region-I ("`C_L`-term") estimate of the numeric core `Work.FIArea7.NumericCore`
(`Area7Assembly6.lean`): under the *FI* side conditions `X ^ 8 ≤ N ^ δ₁` (`δ₁ < 3/32`) and
`X³(log(N+2))²⁰ ≤ K ≤ 2X³(log(N+2))²⁰`, the region-I summand is `O(X⁻¹ N² log N)`,
uniformly in `X`, `N`, `K`.
-/
import Mathlib
import Submission.Work.FIArea7.NCBasic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7

/-! ## Auxiliary estimates -/

/-- `log (K+2) ≤ 30 log (N+2)` in the *FI* range `X⁸ ≤ N^{δ₁}`, `δ₁ < 3/32`. -/
private lemma ncl_log_K_le (N X δ₁ L : ℝ) (K : ℕ) (hN : 3 ≤ N) (hδ32 : δ₁ < 3 / 32)
    (hX : 1 ≤ X) (hXδ : X ^ 8 ≤ N ^ δ₁) (hL : L = Real.log (N + 2))
    (hKhigh : (K : ℝ) ≤ 2 * X ^ 3 * L ^ 20) :
    Real.log ((K : ℝ) + 2) ≤ 30 * L := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact le_trans (one_le_log_of_three_le hN) (Real.log_le_log hNpos (by linarith))
  have hLpos : (0 : ℝ) < L := by linarith
  have hlogX : Real.log X ≤ L := by
    have hXle : X ≤ N ^ (δ₁ / 8) := le_rpow_div_eight_of_pow_eight_le hX0 hNpos hXδ
    have hXleN : X ≤ N := by
      calc X ≤ N ^ (δ₁ / 8) := hXle
        _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hδ32])
        _ = N := Real.rpow_one N
    rw [hL]
    exact Real.log_le_log hXpos (by linarith)
  have hX3ne : X ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hXpos)
  have hL20ne : L ^ 20 ≠ 0 := pow_ne_zero 20 (ne_of_gt hLpos)
  have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hL20 : 1 ≤ L ^ 20 := one_le_pow₀ hL1
  have hprod : 1 ≤ X ^ 3 * L ^ 20 := by nlinarith [hX3, hL20]
  have hK2 : (K : ℝ) + 2 ≤ 4 * (X ^ 3 * L ^ 20) := by
    have h1 : (K : ℝ) ≤ 2 * (X ^ 3 * L ^ 20) := by
      calc (K : ℝ) ≤ 2 * X ^ 3 * L ^ 20 := hKhigh
        _ = 2 * (X ^ 3 * L ^ 20) := by ring
    nlinarith [h1, hprod]
  have hsplit : Real.log (4 * (X ^ 3 * L ^ 20))
      = Real.log 4 + (3 : ℝ) * Real.log X + (20 : ℝ) * Real.log L := by
    rw [Real.log_mul (by norm_num) (mul_ne_zero hX3ne hL20ne),
        Real.log_mul hX3ne hL20ne, Real.log_pow, Real.log_pow]
    ring
  calc Real.log ((K : ℝ) + 2) ≤ Real.log (4 * (X ^ 3 * L ^ 20)) :=
        Real.log_le_log (by linarith) hK2
    _ = Real.log 4 + (3 : ℝ) * Real.log X + (20 : ℝ) * Real.log L := hsplit
    _ ≤ 30 * L := by
        have h4 : Real.log 4 ≤ 4 * L := by
          have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
          nlinarith [h, hL1]
        have hXb : (3 : ℝ) * Real.log X ≤ 3 * L := by nlinarith [hlogX]
        have hLb : (20 : ℝ) * Real.log L ≤ 20 * L := by
          have h := Real.log_le_self hLpos.le
          nlinarith [h]
        linarith

/-- `√(θ+1)` and `(θ+1)^{3/2}` bounds for `θ = N^{δ₁}/(2K+1)`, together with `X⁸ ≤ N^{δ₁}`. -/
private lemma ncl_bracket_le (N X δ₁ θ : ℝ) (K : ℕ) (hN : 3 ≤ N) (hδ0 : 0 < δ₁)
    (hX : 1 ≤ X) (hXδ : X ^ 8 ≤ N ^ δ₁) (hK : 1 ≤ (K : ℝ))
    (hθ : θ = N ^ δ₁ / (2 * (K : ℝ) + 1)) :
    X ^ 2 * Real.sqrt (θ + 1) + X * (θ + 1) ^ ((3 : ℝ) / 2) ≤ 5 * N ^ (13 * δ₁ / 8) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hden : (1 : ℝ) ≤ 2 * (K : ℝ) + 1 := by linarith
  have hNδnn : 0 ≤ N ^ δ₁ := Real.rpow_nonneg hNpos.le δ₁
  have hNδ1 : 1 ≤ N ^ δ₁ := Real.one_le_rpow hN1 hδ0.le
  have hθnn : 0 ≤ θ := by rw [hθ]; exact div_nonneg hNδnn (by linarith)
  have hθle : θ ≤ N ^ δ₁ := by rw [hθ]; exact div_le_self hNδnn hden
  have hθ1 : θ + 1 ≤ 2 * N ^ δ₁ := by linarith
  have hθ10 : (0 : ℝ) ≤ θ + 1 := by linarith
  have hsq : Real.sqrt (θ + 1) ≤ 2 * N ^ (δ₁ / 2) := by
    calc Real.sqrt (θ + 1) ≤ Real.sqrt (2 * N ^ δ₁) := Real.sqrt_le_sqrt hθ1
      _ = Real.sqrt 2 * Real.sqrt (N ^ δ₁) := Real.sqrt_mul (by norm_num) _
      _ = Real.sqrt 2 * N ^ (δ₁ / 2) := by
            rw [show Real.sqrt (N ^ δ₁) = N ^ (δ₁ / 2) from by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; congr 1; ring]
      _ ≤ 2 * N ^ (δ₁ / 2) :=
            mul_le_mul_of_nonneg_right sqrt_two_le_two (Real.rpow_nonneg hNpos.le _)
  have hrp : (θ + 1) ^ ((3 : ℝ) / 2) ≤ 3 * N ^ (3 * δ₁ / 2) := by
    have h1 : (θ + 1) ^ ((3 : ℝ) / 2) ≤ (2 * N ^ δ₁) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hθ10 hθ1 (by norm_num)
    have h2 : (2 * N ^ δ₁) ^ ((3 : ℝ) / 2) = 2 ^ ((3 : ℝ) / 2) * N ^ (3 * δ₁ / 2) := by
      rw [Real.mul_rpow (by norm_num) hNδnn, ← Real.rpow_mul hNpos.le]
      congr 2; ring
    have h3 : 2 ^ ((3 : ℝ) / 2) * N ^ (3 * δ₁ / 2) ≤ 3 * N ^ (3 * δ₁ / 2) :=
      mul_le_mul_of_nonneg_right two_rpow_three_halves_le_three (Real.rpow_nonneg hNpos.le _)
    calc (θ + 1) ^ ((3 : ℝ) / 2) ≤ 2 ^ ((3 : ℝ) / 2) * N ^ (3 * δ₁ / 2) :=
          le_trans h1 (le_of_eq h2)
      _ ≤ 3 * N ^ (3 * δ₁ / 2) := h3
  have hXle : X ≤ N ^ (δ₁ / 8) := le_rpow_div_eight_of_pow_eight_le hX0 hNpos hXδ
  have hXsq : X ^ 2 ≤ N ^ (δ₁ / 4) := by
    have h := pow_le_pow_left₀ hX0 hXle 2
    have h2 : (N ^ (δ₁ / 8)) ^ 2 = N ^ (δ₁ / 4) := by
      rw [← Real.rpow_natCast (N ^ (δ₁ / 8)) 2, ← Real.rpow_mul hNpos.le]; congr 1; ring
    rw [h2] at h; exact h
  have hterm1 : X ^ 2 * Real.sqrt (θ + 1) ≤ 2 * N ^ (13 * δ₁ / 8) := by
    have hmul : X ^ 2 * Real.sqrt (θ + 1) ≤ N ^ (δ₁ / 4) * (2 * N ^ (δ₁ / 2)) :=
      mul_le_mul hXsq hsq (Real.sqrt_nonneg _) (Real.rpow_nonneg hNpos.le _)
    have heq : N ^ (δ₁ / 4) * (2 * N ^ (δ₁ / 2)) = 2 * N ^ (3 * δ₁ / 4) := by
      have h : N ^ (δ₁ / 4) * N ^ (δ₁ / 2) = N ^ (3 * δ₁ / 4) := by
        rw [← Real.rpow_add hNpos]; congr 1; ring
      calc N ^ (δ₁ / 4) * (2 * N ^ (δ₁ / 2)) = 2 * (N ^ (δ₁ / 4) * N ^ (δ₁ / 2)) := by ring
        _ = 2 * N ^ (3 * δ₁ / 4) := by rw [h]
    have hle : 2 * N ^ (3 * δ₁ / 4) ≤ 2 * N ^ (13 * δ₁ / 8) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hδ0])) (by norm_num)
    calc X ^ 2 * Real.sqrt (θ + 1) ≤ N ^ (δ₁ / 4) * (2 * N ^ (δ₁ / 2)) := hmul
      _ = 2 * N ^ (3 * δ₁ / 4) := heq
      _ ≤ 2 * N ^ (13 * δ₁ / 8) := hle
  have hterm2 : X * (θ + 1) ^ ((3 : ℝ) / 2) ≤ 3 * N ^ (13 * δ₁ / 8) := by
    have hmul : X * (θ + 1) ^ ((3 : ℝ) / 2) ≤ N ^ (δ₁ / 8) * (3 * N ^ (3 * δ₁ / 2)) :=
      mul_le_mul hXle hrp (Real.rpow_nonneg hθ10 _) (Real.rpow_nonneg hNpos.le _)
    have heq : N ^ (δ₁ / 8) * (3 * N ^ (3 * δ₁ / 2)) = 3 * N ^ (13 * δ₁ / 8) := by
      have h : N ^ (δ₁ / 8) * N ^ (3 * δ₁ / 2) = N ^ (13 * δ₁ / 8) := by
        rw [← Real.rpow_add hNpos]; congr 1; ring
      calc N ^ (δ₁ / 8) * (3 * N ^ (3 * δ₁ / 2)) = 3 * (N ^ (δ₁ / 8) * N ^ (3 * δ₁ / 2)) := by ring
        _ = 3 * N ^ (13 * δ₁ / 8) := by rw [h]
    calc X * (θ + 1) ^ ((3 : ℝ) / 2) ≤ N ^ (δ₁ / 8) * (3 * N ^ (3 * δ₁ / 2)) := hmul
      _ = 3 * N ^ (13 * δ₁ / 8) := heq
  calc X ^ 2 * Real.sqrt (θ + 1) + X * (θ + 1) ^ ((3 : ℝ) / 2)
      ≤ 2 * N ^ (13 * δ₁ / 8) + 3 * N ^ (13 * δ₁ / 8) := add_le_add hterm1 hterm2
    _ = 5 * N ^ (13 * δ₁ / 8) := by ring

/-- `(log(N+2))² N^{-c} ≤ (4/c) log N` for `N ≥ 3`, `c > 0`. -/
private lemma ncl_log_sq_decay (N c : ℝ) (hN : 3 ≤ N) (hc : 0 < c) :
    (Real.log (N + 2)) ^ 2 * N ^ (-c) ≤ (4 / c) * Real.log N := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL2 : Real.log (N + 2) ≤ 2 * Real.log N := log_add_two_le_two_mul_log (by linarith)
  have hL0 : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hLsq : (Real.log (N + 2)) ^ 2 ≤ 4 * (Real.log N) ^ 2 := by
    have h := pow_le_pow_left₀ hL0 hL2 2
    have h2 : (2 * Real.log N) ^ 2 = 4 * (Real.log N) ^ 2 := by ring
    rw [h2] at h; exact h
  have hlog_le : Real.log N ≤ N ^ c / c := Real.log_le_rpow_div hNpos.le hc
  have hcancel : N ^ c * N ^ (-c) = 1 := by
    rw [← Real.rpow_add hNpos, show c + (-c) = 0 by ring, Real.rpow_zero]
  have hstep : Real.log N * N ^ (-c) ≤ 1 / c := by
    have h1 : Real.log N * N ^ (-c) ≤ (N ^ c / c) * N ^ (-c) :=
      mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg hNpos.le _)
    have h2 : (N ^ c / c) * N ^ (-c) = 1 / c := by
      rw [div_mul_eq_mul_div, hcancel]
    linarith [h1, h2]
  calc (Real.log (N + 2)) ^ 2 * N ^ (-c)
      ≤ (4 * (Real.log N) ^ 2) * N ^ (-c) :=
        mul_le_mul_of_nonneg_right hLsq (Real.rpow_nonneg hNpos.le _)
    _ = 4 * (Real.log N * (Real.log N * N ^ (-c))) := by ring
    _ ≤ 4 * (Real.log N * (1 / c)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hstep hlogN0
    _ = (4 / c) * Real.log N := by ring

/-! ## The region-I term bound -/

theorem nc_termL (C_L c₁ δ₁ : ℝ) (hCL : 0 < C_L) (hc₁ : 0 < c₁) (hδ0 : 0 < δ₁)
    (hδ32 : δ₁ < 3 / 32) :
    ∃ N₀ M : ℝ, 0 < M ∧ ∀ {N X : ℝ} {K : ℕ},
      3 ≤ N → N₀ ≤ N → 1 ≤ X → X ^ 8 ≤ N ^ δ₁ → 1 ≤ (K : ℝ) →
      X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
      (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
      C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1)
              + (N ^ δ₁ / (2 * (K : ℝ) + 1) + 1) ^ ((3 : ℝ) / 2))
        ≤ M * X⁻¹ * N ^ 2 * Real.log N := by
  refine ⟨3, C_L * c₁ ^ 2 * 57600 / δ₁, by positivity, ?_⟩
  intro N X K hN hN0 hX hX8 hK1 hKlow hKhigh
  set L : ℝ := Real.log (N + 2) with hL
  set θ : ℝ := N ^ δ₁ / (2 * (K : ℝ) + 1) with hθ
  set M : ℝ := C_L * c₁ ^ 2 * 57600 / δ₁ with hM
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogN1 : 1 ≤ Real.log N := one_le_log_of_three_le hN
  have hlogN0 : 0 ≤ Real.log N := le_trans zero_le_one hlogN1
  have hlogK : Real.log ((K : ℝ) + 2) ≤ 30 * L :=
    ncl_log_K_le N X δ₁ L K hN hδ32 hX hX8 hL hKhigh
  have hlogKsq : (Real.log ((K : ℝ) + 2)) ^ 2 ≤ 900 * L ^ 2 := by
    have h0 : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h := pow_le_pow_left₀ h0 hlogK 2
    have h2 : (30 * L) ^ 2 = 900 * L ^ 2 := by ring
    rw [h2] at h; exact h
  have hbracket : X ^ 2 * Real.sqrt (θ + 1) + X * (θ + 1) ^ ((3 : ℝ) / 2)
      ≤ 5 * N ^ (13 * δ₁ / 8) :=
    ncl_bracket_le N X δ₁ θ K hN hδ0 hX hX8 hK1 hθ
  have hprod : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X ^ 2 * Real.sqrt (θ + 1) + X * (θ + 1) ^ ((3 : ℝ) / 2))
      ≤ C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (900 * L ^ 2) * (5 * N ^ (13 * δ₁ / 8)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hlogKsq (by positivity)
    · exact hbracket
    · positivity
    · positivity
  have hstep1 : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (900 * L ^ 2) * (5 * N ^ (13 * δ₁ / 8))
      ≤ 4500 * C_L * c₁ ^ 2 * N ^ 2 * ((32 / (3 * δ₁)) * Real.log N) := by
    have hexp : N ^ (2 - 2 * δ₁) * N ^ (13 * δ₁ / 8) = N ^ 2 * N ^ (-(3 * δ₁ / 8)) := by
      rw [← Real.rpow_add hNpos]
      rw [show 2 - 2 * δ₁ + 13 * δ₁ / 8 = 2 + (-(3 * δ₁ / 8)) by ring]
      rw [Real.rpow_add hNpos]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hdec : L ^ 2 * N ^ (-(3 * δ₁ / 8)) ≤ (32 / (3 * δ₁)) * Real.log N := by
      have h := ncl_log_sq_decay N (3 * δ₁ / 8) hN (by positivity)
      have heq : 4 / (3 * δ₁ / 8) = 32 / (3 * δ₁) := by field_simp; ring
      calc L ^ 2 * N ^ (-(3 * δ₁ / 8)) ≤ (4 / (3 * δ₁ / 8)) * Real.log N := h
        _ = (32 / (3 * δ₁)) * Real.log N := by rw [heq]
    calc C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (900 * L ^ 2) * (5 * N ^ (13 * δ₁ / 8))
        = 4500 * C_L * c₁ ^ 2 * (N ^ (2 - 2 * δ₁) * N ^ (13 * δ₁ / 8)) * L ^ 2 := by ring
      _ = 4500 * C_L * c₁ ^ 2 * (N ^ 2 * N ^ (-(3 * δ₁ / 8))) * L ^ 2 := by rw [hexp]
      _ = 4500 * C_L * c₁ ^ 2 * N ^ 2 * (L ^ 2 * N ^ (-(3 * δ₁ / 8))) := by ring
      _ ≤ 4500 * C_L * c₁ ^ 2 * N ^ 2 * ((32 / (3 * δ₁)) * Real.log N) := by
            apply mul_le_mul_of_nonneg_left hdec; positivity
  have hstep2 : 4500 * C_L * c₁ ^ 2 * N ^ 2 * ((32 / (3 * δ₁)) * Real.log N)
      ≤ M * N ^ 2 * Real.log N := by
    rw [hM]
    have hcoeff : (4500 : ℝ) * (32 / (3 * δ₁)) ≤ 57600 / δ₁ := by
      have he : (4500 : ℝ) * (32 / (3 * δ₁)) = 48000 / δ₁ := by field_simp; ring
      rw [he]
      exact div_le_div_of_nonneg_right (by norm_num) hδ0.le
    calc 4500 * C_L * c₁ ^ 2 * N ^ 2 * ((32 / (3 * δ₁)) * Real.log N)
        = (C_L * c₁ ^ 2 * N ^ 2 * Real.log N) * ((4500 : ℝ) * (32 / (3 * δ₁))) := by ring
      _ ≤ (C_L * c₁ ^ 2 * N ^ 2 * Real.log N) * (57600 / δ₁) :=
            mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = C_L * c₁ ^ 2 * 57600 / δ₁ * N ^ 2 * Real.log N := by ring
  have hfinal : X * (C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * Real.sqrt (θ + 1) + (θ + 1) ^ ((3 : ℝ) / 2)))
      ≤ M * N ^ 2 * Real.log N := by
    have hre : X * (C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (θ + 1) + (θ + 1) ^ ((3 : ℝ) / 2)))
        = C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X ^ 2 * Real.sqrt (θ + 1) + X * (θ + 1) ^ ((3 : ℝ) / 2)) := by ring
    rw [hre]
    exact le_trans hprod (le_trans hstep1 hstep2)
  have hmain : C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
        * (X * Real.sqrt (θ + 1) + (θ + 1) ^ ((3 : ℝ) / 2))
      ≤ M * X⁻¹ * N ^ 2 * Real.log N := by
    have h := mul_le_mul_of_nonneg_left hfinal (le_of_lt (inv_pos.mpr hXpos))
    have h1 : X⁻¹ * (X * (C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (θ + 1) + (θ + 1) ^ ((3 : ℝ) / 2))))
        = C_L * c₁ ^ 2 * N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * Real.sqrt (θ + 1) + (θ + 1) ^ ((3 : ℝ) / 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hXpos), one_mul]
    have h2 : X⁻¹ * (M * N ^ 2 * Real.log N) = M * X⁻¹ * N ^ 2 * Real.log N := by ring
    rw [h1, h2] at h
    exact h
  exact hmain

end Work.FIArea7
