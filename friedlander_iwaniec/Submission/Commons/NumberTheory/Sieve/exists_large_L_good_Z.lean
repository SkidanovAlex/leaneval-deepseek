import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.NumberTheory.Sieve

open Filter Asymptotics

/-! ## Elementary asymptotic helpers -/

/-- For any `A D : ℝ`, `E r : ℝ` with `E > 0`, `r > 0`, eventually
`A + D * log L ≤ E * L ^ r`. -/
lemma eventually_add_log_le_rpow (A D E r : ℝ) (hE : 0 < E) (hr : 0 < r) :
    ∀ᶠ L in atTop, A + D * Real.log L ≤ E * L ^ r := by
  have hg : Tendsto (fun x : ℝ => ‖x ^ r‖) atTop atTop := by
    rw [tendsto_atTop] at ⊢
    intro b
    filter_upwards [tendsto_rpow_atTop hr |>.eventually_ge_atTop (max b 0)] with x hx
    rw [Real.norm_of_nonneg (le_trans (le_max_right _ _) hx)]
    exact le_trans (le_max_left _ _) hx
  have hconst : (fun _ : ℝ => A) =o[atTop] (fun x : ℝ => x ^ r) := by
    rw [isLittleO_const_left]; exact Or.inr hg
  have hlogD : (fun x : ℝ => D * Real.log x) =o[atTop] (fun x : ℝ => x ^ r) :=
    (isLittleO_log_rpow_atTop hr).const_mul_left D
  have hsum : (fun x : ℝ => A + D * Real.log x) =o[atTop] (fun x : ℝ => x ^ r) := by
    have := hconst.add hlogD; simpa using this
  filter_upwards [hsum.bound hE, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hrp : 0 ≤ x ^ r := Real.rpow_nonneg hx0 r
  have hx' : |A + D * Real.log x| ≤ E * x ^ r := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hrp] using hx
  calc A + D * Real.log x ≤ |A + D * Real.log x| := le_abs_self _
    _ ≤ E * x ^ r := hx'

/-- `c * L / (B * L^(8/9)) = (c / B) * L^(1/9)` for `L > 0`. -/
lemma mul_div_rpow_gen (c B L : ℝ) (hL : 0 < L) :
    c * L / (B * L ^ (8 / 9 : ℝ)) = (c / B) * L ^ (1 / 9 : ℝ) := by
  have hL9 : L ^ (1 / 9 : ℝ) = L / L ^ (8 / 9 : ℝ) := by
    rw [show (1 / 9 : ℝ) = 1 - 8 / 9 by norm_num, Real.rpow_sub hL, Real.rpow_one]
  rw [hL9, div_mul_div_comm]

lemma rpow_eight_ninths_pow_nine {L : ℝ} (hL : 0 ≤ L) :
    (L ^ (8 / 9 : ℝ)) ^ 9 = L ^ 8 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

lemma exp_half_eq_sqrt_exp (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

lemma eventually_two_mul_pow_ten_le_exp_half :
    ∀ᶠ x in atTop, (2 * x) ^ 10 ≤ Real.exp (x / 2) := by
  have h1 : (fun x : ℝ => x ^ 10) =o[atTop] (fun x : ℝ => Real.exp (x / 2)) := by
    have h0 := isLittleO_pow_exp_pos_mul_atTop 10 (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa [one_div, div_eq_mul_inv, mul_comm] using h0
  have h2 : (fun x : ℝ => (2 * x) ^ 10) =o[atTop] (fun x : ℝ => Real.exp (x / 2)) := by
    simpa [mul_pow] using h1.const_mul_left ((2 : ℝ) ^ 10)
  filter_upwards [h2.bound (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hxn : 0 ≤ (2 * x) ^ 10 := by positivity
  have hexp : 0 ≤ Real.exp (x / 2) := (Real.exp_pos _).le
  simpa only [Real.norm_of_nonneg hxn, Real.norm_of_nonneg hexp, one_mul] using hx

/-! ## The candidate `Z` -/

/-- `goodY k L = k * L^(8/9) + 200`. -/
noncomputable def goodY (k L : ℝ) : ℝ := k * L ^ (8 / 9 : ℝ) + 200

/-- The candidate choice of `Z`. -/
noncomputable def goodZ (k L : ℝ) : ℕ := Nat.ceil (Real.exp (goodY k L))

lemma goodY_ge_const {k : ℝ} (hk : 0 ≤ k) {L : ℝ} (hL : 0 ≤ L) : 200 ≤ goodY k L := by
  have h : 0 ≤ k * L ^ (8 / 9 : ℝ) := mul_nonneg hk (Real.rpow_nonneg hL _)
  simp only [goodY]; linarith

lemma goodY_ge_rpow (k L : ℝ) : k * L ^ (8 / 9 : ℝ) ≤ goodY k L := by
  simp only [goodY]; linarith

lemma exp_goodY_le_goodZ (k L : ℝ) : Real.exp (goodY k L) ≤ (goodZ k L : ℝ) := by
  simp only [goodZ]; exact Nat.le_ceil _

lemma goodY_le_log_goodZ (k L : ℝ) : goodY k L ≤ Real.log (goodZ k L : ℝ) := by
  have h := Real.log_le_log (Real.exp_pos (goodY k L)) (exp_goodY_le_goodZ k L)
  rwa [Real.log_exp] at h

lemma goodZ_lt_exp_goodY_add_one (k L : ℝ) :
    (goodZ k L : ℝ) < Real.exp (goodY k L) + 1 := by
  simp only [goodZ]
  exact Nat.ceil_lt_add_one (Real.exp_pos (goodY k L)).le

lemma log_goodZ_pos {k : ℝ} (hk : 0 ≤ k) {L : ℝ} (hL : 0 ≤ L) :
    0 < Real.log (goodZ k L : ℝ) :=
  lt_of_lt_of_le (by norm_num) (le_trans (goodY_ge_const hk hL) (goodY_le_log_goodZ k L))

lemma log_goodZ_nonneg {k : ℝ} (hk : 0 ≤ k) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ Real.log (goodZ k L : ℝ) := le_of_lt (log_goodZ_pos hk hL)

lemma log_goodZ_le_two_goodY {k : ℝ} (hk : 0 ≤ k) {L : ℝ} (hL : 0 ≤ L) :
    Real.log (goodZ k L : ℝ) ≤ 2 * goodY k L := by
  have hy1 : (1 : ℝ) ≤ goodY k L := le_trans (by norm_num) (goodY_ge_const hk hL)
  have hpos : 0 < (goodZ k L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) (exp_goodY_le_goodZ k L)
  have hlt : (goodZ k L : ℝ) < Real.exp (2 * goodY k L) := by
    have h1 := goodZ_lt_exp_goodY_add_one k L
    have h2 : (2 : ℝ) ≤ Real.exp (goodY k L) :=
      le_trans (le_of_lt Real.exp_one_gt_two) (Real.exp_le_exp_of_le hy1)
    calc (goodZ k L : ℝ) < Real.exp (goodY k L) + 1 := h1
      _ ≤ 2 * Real.exp (goodY k L) := by linarith
      _ ≤ Real.exp (goodY k L) * Real.exp (goodY k L) := by nlinarith [h2]
      _ = Real.exp (goodY k L + goodY k L) := (Real.exp_add _ _).symm
      _ = Real.exp (2 * goodY k L) := by
            rw [show goodY k L + goodY k L = 2 * goodY k L by ring]
  calc Real.log (goodZ k L : ℝ) ≤ Real.log (Real.exp (2 * goodY k L)) :=
        Real.log_le_log hpos (le_of_lt hlt)
    _ = 2 * goodY k L := Real.log_exp _

lemma exp_half_le_sqrt_goodZ (k L : ℝ) :
    Real.exp (goodY k L / 2) ≤ Real.sqrt (goodZ k L : ℝ) := by
  have h1 : Real.sqrt (Real.exp (goodY k L)) ≤ Real.sqrt (goodZ k L : ℝ) :=
    Real.sqrt_le_sqrt (exp_goodY_le_goodZ k L)
  rwa [exp_half_eq_sqrt_exp] at h1

lemma goodY_le_mul {k : ℝ} {L B : ℝ} (hL : 1 ≤ L) (hB : B = k + 200) :
    goodY k L ≤ B * L ^ (8 / 9 : ℝ) := by
  have hLr : (1 : ℝ) ≤ L ^ (8 / 9 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have h1 : (200 : ℝ) ≤ 200 * L ^ (8 / 9 : ℝ) := by nlinarith
  rw [goodY, hB]
  nlinarith [h1]

lemma log_goodZ_le {k : ℝ} (hk : 0 ≤ k) {L B : ℝ} (hL : 1 ≤ L) (hB : B = k + 200) :
    Real.log (goodZ k L : ℝ) ≤ 2 * B * L ^ (8 / 9 : ℝ) := by
  calc Real.log (goodZ k L : ℝ) ≤ 2 * goodY k L := log_goodZ_le_two_goodY hk (by linarith)
    _ ≤ 2 * (B * L ^ (8 / 9 : ℝ)) := by
        have := goodY_le_mul hL hB; linarith
    _ = 2 * B * L ^ (8 / 9 : ℝ) := by ring

lemma log_log_goodZ_le {k : ℝ} (hk : 0 ≤ k) {L B : ℝ} (hL : 1 ≤ L) (hB : B = k + 200) :
    Real.log (Real.log (goodZ k L : ℝ)) ≤ Real.log (2 * B) + (8 / 9) * Real.log L := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hBpos : 0 < B := by rw [hB]; linarith
  have hlogZ_le : Real.log (goodZ k L : ℝ) ≤ 2 * B * L ^ (8 / 9 : ℝ) :=
    log_goodZ_le hk hL hB
  have hpos : 0 < Real.log (goodZ k L : ℝ) := log_goodZ_pos hk (by linarith)
  calc Real.log (Real.log (goodZ k L : ℝ))
      ≤ Real.log (2 * B * L ^ (8 / 9 : ℝ)) := Real.log_le_log hpos hlogZ_le
    _ = Real.log (2 * B) + Real.log (L ^ (8 / 9 : ℝ)) := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) hBpos.ne')
          (Real.rpow_pos_of_pos hL0 _).ne']
    _ = Real.log (2 * B) + (8 / 9) * Real.log L := by rw [Real.log_rpow hL0]

/-! ## The main theorem -/

theorem exists_large_L_good_Z
    (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : 0 < c) (γ δ : ℝ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ Z : ℕ,
      3 ≤ Z ∧
      200 ≤ Real.log (Z : ℝ) ∧
      (Real.log (Z : ℝ)) ^ 10 ≤ Real.sqrt (Z : ℝ) ∧
      4 * Real.log (Z : ℝ) ≤ L ∧
      3 * α * L ^ 8 ≤ (Real.log (Z : ℝ)) ^ 9 ∧
      Real.log (3 * α * Real.log (Z : ℝ)) + 6 * Real.log L ≤ c * L / Real.log (Z : ℝ) ∧
      (δ + 6 * Real.log L + 7 * Real.log (Real.log (Z : ℝ))) ≤ L / (4 * Real.log (Z : ℝ)) ∧
      (γ + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ))) ≤ L / (4 * Real.log (Z : ℝ)) := by
  set k : ℝ := (3 * α) ^ (1 / 9 : ℝ) with hk
  have hkpos : 0 < k := by rw [hk]; exact Real.rpow_pos_of_pos (by positivity) _
  have hkle : 0 ≤ k := le_of_lt hkpos
  have hk9 : k ^ 9 = 3 * α := by
    rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3 * α)]
    norm_num
  set B : ℝ := k + 200 with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  have hLe : ∀ᶠ L : ℝ in atTop, (1 : ℝ) ≤ L := eventually_ge_atTop 1
  have hy_tendsto : Tendsto (fun L : ℝ => goodY k L) atTop atTop := by
    rw [tendsto_atTop] at ⊢
    intro b
    have hkL : Tendsto (fun L : ℝ => k * L ^ (8 / 9 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 9)).const_mul_atTop hkpos
    filter_upwards [hkL.eventually_ge_atTop (b - 200)] with L hL
    rw [goodY]; linarith
  -- (C1) `3 ≤ Z`
  have hC1 : ∀ᶠ L : ℝ in atTop, 3 ≤ goodZ k L := by
    filter_upwards [hLe] with L hL
    have h3 : (3 : ℝ) ≤ Real.exp (goodY k L) := by
      refine (Real.log_le_iff_le_exp (show (0 : ℝ) < 3 by norm_num)).mp ?_
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      have h200 : 200 ≤ goodY k L := goodY_ge_const hkle (by linarith)
      linarith
    have h := le_trans h3 (exp_goodY_le_goodZ k L)
    exact_mod_cast h
  -- (C2) `200 ≤ log Z`
  have hC2 : ∀ᶠ L : ℝ in atTop, 200 ≤ Real.log (goodZ k L : ℝ) := by
    filter_upwards [hLe] with L hL
    exact le_trans (goodY_ge_const hkle (by linarith)) (goodY_le_log_goodZ k L)
  -- (C3) `(log Z)^10 ≤ sqrt Z`
  have hC3 : ∀ᶠ L : ℝ in atTop,
      (Real.log (goodZ k L : ℝ)) ^ 10 ≤ Real.sqrt (goodZ k L : ℝ) := by
    have hpy : ∀ᶠ L : ℝ in atTop,
        (2 * goodY k L) ^ 10 ≤ Real.exp (goodY k L / 2) :=
      hy_tendsto.eventually eventually_two_mul_pow_ten_le_exp_half
    filter_upwards [hpy, hLe] with L hL hL0
    calc (Real.log (goodZ k L : ℝ)) ^ 10 ≤ (2 * goodY k L) ^ 10 :=
          pow_le_pow_left₀ (log_goodZ_nonneg hkle (by linarith)) (log_goodZ_le_two_goodY hkle (by linarith)) 10
      _ ≤ Real.exp (goodY k L / 2) := hL
      _ ≤ Real.sqrt (goodZ k L : ℝ) := exp_half_le_sqrt_goodZ k L
  -- (C4) `4 log Z ≤ L`
  have hC4 : ∀ᶠ L : ℝ in atTop, 4 * Real.log (goodZ k L : ℝ) ≤ L := by
    have h1 : ∀ᶠ L : ℝ in atTop, Real.log (goodZ k L : ℝ) ≤ 2 * B * L ^ (8 / 9 : ℝ) := by
      filter_upwards [hLe] with L hL
      exact log_goodZ_le hkle hL hB
    have h2 : ∀ᶠ L : ℝ in atTop, 8 * B * L ^ (8 / 9 : ℝ) ≤ L := by
      have h9 : ∀ᶠ L : ℝ in atTop, (8 * B : ℝ) ≤ L ^ (1 / 9 : ℝ) :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).eventually_ge_atTop (8 * B)
      filter_upwards [h9, hLe] with L h9L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hLr : 0 < L ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hL0 _
      have hsplit : L ^ (1 / 9 : ℝ) * L ^ (8 / 9 : ℝ) = L := by
        rw [← Real.rpow_add hL0]; norm_num
      calc 8 * B * L ^ (8 / 9 : ℝ) ≤ L ^ (1 / 9 : ℝ) * L ^ (8 / 9 : ℝ) := by nlinarith
        _ = L := hsplit
    filter_upwards [h1, h2] with L h1L h2L
    calc 4 * Real.log (goodZ k L : ℝ) ≤ 4 * (2 * B * L ^ (8 / 9 : ℝ)) := by linarith
      _ = 8 * B * L ^ (8 / 9 : ℝ) := by ring
      _ ≤ L := h2L
  -- (C5) `3 α L^8 ≤ (log Z)^9`
  have hC5 : ∀ᶠ L : ℝ in atTop, 3 * α * L ^ 8 ≤ (Real.log (goodZ k L : ℝ)) ^ 9 := by
    filter_upwards [hLe] with L hL1
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hstep : k * L ^ (8 / 9 : ℝ) ≤ Real.log (goodZ k L : ℝ) :=
      le_trans (goodY_ge_rpow k L) (goodY_le_log_goodZ k L)
    have hkL0 : 0 ≤ k * L ^ (8 / 9 : ℝ) := mul_nonneg hkle (Real.rpow_nonneg hL0.le _)
    have hpow := pow_le_pow_left₀ hkL0 hstep 9
    have hLrpow : (L ^ (8 / 9 : ℝ)) ^ 9 = L ^ 8 := rpow_eight_ninths_pow_nine hL0.le
    calc 3 * α * L ^ 8 = k ^ 9 * L ^ 8 := by rw [hk9]
      _ = k ^ 9 * (L ^ (8 / 9 : ℝ)) ^ 9 := by rw [hLrpow]
      _ = (k * L ^ (8 / 9 : ℝ)) ^ 9 := by rw [mul_pow]
      _ ≤ (Real.log (goodZ k L : ℝ)) ^ 9 := hpow
  -- (C6) `log(3α log Z) + 6 log L ≤ c L / log Z`
  have hC6 : ∀ᶠ L : ℝ in atTop,
      Real.log (3 * α * Real.log (goodZ k L : ℝ)) + 6 * Real.log L
        ≤ c * L / Real.log (goodZ k L : ℝ) := by
    have hE6 : 0 < c / (2 * B) := by positivity
    have hup : ∀ᶠ L : ℝ in atTop,
        Real.log (3 * α * Real.log (goodZ k L : ℝ))
          ≤ Real.log (6 * α * B) + (8 / 9) * Real.log L := by
      filter_upwards [hLe] with L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hlogZ_le : Real.log (goodZ k L : ℝ) ≤ 2 * B * L ^ (8 / 9 : ℝ) :=
        log_goodZ_le hkle hL1 hB
      have hle : 3 * α * Real.log (goodZ k L : ℝ) ≤ 6 * α * B * L ^ (8 / 9 : ℝ) := by
        have h3a : (0 : ℝ) < 3 * α := by positivity
        nlinarith [hlogZ_le, h3a]
      calc Real.log (3 * α * Real.log (goodZ k L : ℝ))
          ≤ Real.log (6 * α * B * L ^ (8 / 9 : ℝ)) :=
              Real.log_le_log (mul_pos (by positivity : (0 : ℝ) < 3 * α) (log_goodZ_pos hkle hL0.le)) hle
        _ = Real.log (6 * α * B) + Real.log (L ^ (8 / 9 : ℝ)) := by
              rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) hα.ne') hBpos.ne')
                (Real.rpow_pos_of_pos hL0 _).ne']
        _ = Real.log (6 * α * B) + (8 / 9) * Real.log L := by rw [Real.log_rpow hL0]
    have hdom := eventually_add_log_le_rpow (Real.log (6 * α * B)) (62 / 9) (c / (2 * B))
      (1 / 9) hE6 (by norm_num)
    have hlow : ∀ᶠ L : ℝ in atTop,
        (c / (2 * B)) * L ^ (1 / 9 : ℝ) ≤ c * L / Real.log (goodZ k L : ℝ) := by
      filter_upwards [hLe] with L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hlogZpos : 0 < Real.log (goodZ k L : ℝ) := log_goodZ_pos hkle hL0.le
      have hlogZ_le : Real.log (goodZ k L : ℝ) ≤ 2 * goodY k L := log_goodZ_le_two_goodY hkle hL0.le
      have hy_le : goodY k L ≤ B * L ^ (8 / 9 : ℝ) := goodY_le_mul hL1 hB
      have h2ypos : 0 < 2 * goodY k L := by have h := goodY_ge_const hkle hL0.le; linarith
      have hstep1 : c * L / (2 * goodY k L) ≤ c * L / Real.log (goodZ k L : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hlogZpos hlogZ_le
      have hstep2 : c * L / (2 * B * L ^ (8 / 9 : ℝ)) ≤ c * L / (2 * goodY k L) :=
        div_le_div_of_nonneg_left (by positivity) h2ypos (by linarith)
      have heq : c * L / (2 * B * L ^ (8 / 9 : ℝ)) = (c / (2 * B)) * L ^ (1 / 9 : ℝ) :=
        mul_div_rpow_gen c (2 * B) L hL0
      calc (c / (2 * B)) * L ^ (1 / 9 : ℝ) = c * L / (2 * B * L ^ (8 / 9 : ℝ)) := heq.symm
        _ ≤ c * L / (2 * goodY k L) := hstep2
        _ ≤ c * L / Real.log (goodZ k L : ℝ) := hstep1
    filter_upwards [hup, hdom, hlow] with L hupL hdomL hlowL
    calc Real.log (3 * α * Real.log (goodZ k L : ℝ)) + 6 * Real.log L
        ≤ (Real.log (6 * α * B) + (8 / 9) * Real.log L) + 6 * Real.log L := by linarith
      _ = Real.log (6 * α * B) + (62 / 9) * Real.log L := by ring
      _ ≤ (c / (2 * B)) * L ^ (1 / 9 : ℝ) := hdomL
      _ ≤ c * L / Real.log (goodZ k L : ℝ) := hlowL
  -- common lower bound for `L / (4 log Z)`
  have hClow : ∀ᶠ L : ℝ in atTop,
      (1 / (8 * B)) * L ^ (1 / 9 : ℝ) ≤ L / (4 * Real.log (goodZ k L : ℝ)) := by
    filter_upwards [hLe] with L hL1
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hlogZ_le : Real.log (goodZ k L : ℝ) ≤ 2 * goodY k L := log_goodZ_le_two_goodY hkle hL0.le
    have hy_le : goodY k L ≤ B * L ^ (8 / 9 : ℝ) := goodY_le_mul hL1 hB
    have h8ypos : 0 < 8 * goodY k L := by have h := goodY_ge_const hkle hL0.le; linarith
    have h4logpos : 0 < 4 * Real.log (goodZ k L : ℝ) := by
      have h := log_goodZ_pos hkle hL0.le; linarith
    have heq : L / (8 * B * L ^ (8 / 9 : ℝ)) = (1 / (8 * B)) * L ^ (1 / 9 : ℝ) := by
      have h := mul_div_rpow_gen 1 (8 * B) L hL0
      simpa using h
    have hs1 : L / (8 * B * L ^ (8 / 9 : ℝ)) ≤ L / (8 * goodY k L) :=
      div_le_div_of_nonneg_left (by positivity) h8ypos (by linarith)
    have hs2 : L / (8 * goodY k L) ≤ L / (4 * Real.log (goodZ k L : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) h4logpos (by linarith)
    calc (1 / (8 * B)) * L ^ (1 / 9 : ℝ) = L / (8 * B * L ^ (8 / 9 : ℝ)) := heq.symm
      _ ≤ L / (8 * goodY k L) := hs1
      _ ≤ L / (4 * Real.log (goodZ k L : ℝ)) := hs2
  -- (C7) `δ + 6 log L + 7 log log Z ≤ L / (4 log Z)`
  have hC7 : ∀ᶠ L : ℝ in atTop,
      (δ + 6 * Real.log L + 7 * Real.log (Real.log (goodZ k L : ℝ)))
        ≤ L / (4 * Real.log (goodZ k L : ℝ)) := by
    have hE7 : 0 < 1 / (8 * B) := by positivity
    have hup : ∀ᶠ L : ℝ in atTop,
        Real.log (Real.log (goodZ k L : ℝ)) ≤ Real.log (2 * B) + (8 / 9) * Real.log L := by
      filter_upwards [hLe] with L hL1
      exact log_log_goodZ_le hkle hL1 hB
    have hdom := eventually_add_log_le_rpow (δ + 7 * Real.log (2 * B)) (110 / 9) (1 / (8 * B))
      (1 / 9) hE7 (by norm_num)
    filter_upwards [hup, hdom, hClow] with L hupL hdomL hlowL
    calc (δ + 6 * Real.log L + 7 * Real.log (Real.log (goodZ k L : ℝ)))
        ≤ δ + 6 * Real.log L + 7 * (Real.log (2 * B) + (8 / 9) * Real.log L) := by linarith
      _ = (δ + 7 * Real.log (2 * B)) + (110 / 9) * Real.log L := by ring
      _ ≤ (1 / (8 * B)) * L ^ (1 / 9 : ℝ) := hdomL
      _ ≤ L / (4 * Real.log (goodZ k L : ℝ)) := hlowL
  -- (C8) `γ + 8 log L + 8 log log Z ≤ L / (4 log Z)`
  have hC8 : ∀ᶠ L : ℝ in atTop,
      (γ + 8 * Real.log L + 8 * Real.log (Real.log (goodZ k L : ℝ)))
        ≤ L / (4 * Real.log (goodZ k L : ℝ)) := by
    have hE8 : 0 < 1 / (8 * B) := by positivity
    have hup : ∀ᶠ L : ℝ in atTop,
        Real.log (Real.log (goodZ k L : ℝ)) ≤ Real.log (2 * B) + (8 / 9) * Real.log L := by
      filter_upwards [hLe] with L hL1
      exact log_log_goodZ_le hkle hL1 hB
    have hdom := eventually_add_log_le_rpow (γ + 8 * Real.log (2 * B)) (136 / 9) (1 / (8 * B))
      (1 / 9) hE8 (by norm_num)
    filter_upwards [hup, hdom, hClow] with L hupL hdomL hlowL
    calc (γ + 8 * Real.log L + 8 * Real.log (Real.log (goodZ k L : ℝ)))
        ≤ γ + 8 * Real.log L + 8 * (Real.log (2 * B) + (8 / 9) * Real.log L) := by linarith
      _ = (γ + 8 * Real.log (2 * B)) + (136 / 9) * Real.log L := by ring
      _ ≤ (1 / (8 * B)) * L ^ (1 / 9 : ℝ) := hdomL
      _ ≤ L / (4 * Real.log (goodZ k L : ℝ)) := hlowL
  have hall : ∀ᶠ L : ℝ in atTop, ∃ Z : ℕ,
      3 ≤ Z ∧
      200 ≤ Real.log (Z : ℝ) ∧
      (Real.log (Z : ℝ)) ^ 10 ≤ Real.sqrt (Z : ℝ) ∧
      4 * Real.log (Z : ℝ) ≤ L ∧
      3 * α * L ^ 8 ≤ (Real.log (Z : ℝ)) ^ 9 ∧
      Real.log (3 * α * Real.log (Z : ℝ)) + 6 * Real.log L ≤ c * L / Real.log (Z : ℝ) ∧
      (δ + 6 * Real.log L + 7 * Real.log (Real.log (Z : ℝ))) ≤ L / (4 * Real.log (Z : ℝ)) ∧
      (γ + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ))) ≤ L / (4 * Real.log (Z : ℝ)) := by
    filter_upwards [hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8] with L h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨goodZ k L, h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hall
  exact ⟨max L₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun L hL => hL₁ L (le_trans (le_max_left _ _) hL)⟩

end Commons.NumberTheory.Sieve