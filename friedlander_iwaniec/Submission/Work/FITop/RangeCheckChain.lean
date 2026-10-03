/-
# `Work.FITop.RangeCheckChain`

The range check I-0 for the sieve level `Δ = ⌈x^{1/100}⌉` (the parameter set `Lam1, Delta1,
del1, Y1, s1, z1, Pcut, Ctrunc, d2b, Mcutb` of `Submission/Work/FITop/Defs.lean`): all
numerical hypotheses that the chain `ASP.S19` and the window range (4.6) require hold for all
large `x`.  The asymptotics toolkit is `Submission/Work/FITop/RCPrelude.lean`.
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false

namespace Work.FITop

open Filter
open scoped BigOperators

noncomputable section

/-! ## The fourteen conjuncts -/

private lemma RangeC1 (η : ℝ) (hη2 : η < 1 / 16) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < Y1 x / (Delta1 x : ℝ) := by
  filter_upwards [FI_ev_Y1_lower, FI_ev_Delta1_le_two_Lam1, FI_ev_Lam1_ge_one,
    FI_ev_rpow_ge_nat ((9 : ℝ) / 800) (by norm_num) 4, eventually_ge_atTop 2]
    with x hY hD2 hLam hx4 hx2
  have hxpos : (0 : ℝ) < x := by
    have : (0 : ℕ) < x := by omega
    exact_mod_cast this
  have hx1 : (1 : ℝ) < x := by
    have : (1 : ℕ) < x := by omega
    exact_mod_cast this
  have hDpos : 0 < (Delta1 x : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_trans hLam (FI_Lam1_le_Delta1 x))
  have hLam_inv : (Lam1 x)⁻¹ = (x : ℝ) ^ (-((1 : ℝ) / 100)) := by
    rw [Lam1, ← Real.rpow_neg (le_of_lt hxpos) ((1 : ℝ) / 100)]
  have halg : ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x)
      = (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by
    have hpe : (x : ℝ) ^ ((267 : ℝ) / 800) * (x : ℝ) ^ (-((1 : ℝ) / 100))
        = (x : ℝ) ^ ((259 : ℝ) / 800) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    calc ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x)
        = ((x : ℝ) ^ ((267 : ℝ) / 800) * (Lam1 x)⁻¹) / 4 := by ring
      _ = ((x : ℝ) ^ ((267 : ℝ) / 800) * (x : ℝ) ^ (-((1 : ℝ) / 100))) / 4 := by
            rw [hLam_inv]
      _ = ((x : ℝ) ^ ((259 : ℝ) / 800)) / 4 := by rw [hpe]
      _ = (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by ring
  have hstep2 : (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) ≤ Y1 x / (Delta1 x : ℝ) := by
    have h1 : ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x) ≤ Y1 x / (2 * Lam1 x) :=
      div_le_div_of_nonneg_right hY (mul_nonneg (by norm_num) (FI_Lam1_nonneg x))
    have h2 : Y1 x / (2 * Lam1 x) ≤ Y1 x / (Delta1 x : ℝ) :=
      div_le_div_of_nonneg_left (FI_Y1_nonneg x) hDpos hD2
    rw [halg] at h1
    linarith
  have hstep1 : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by
    have hlt5 : (1 : ℝ) / 4 + η < (5 : ℝ) / 16 := by linarith
    have hA5 : 0 ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hchain : (x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((9 : ℝ) / 800)
        = (x : ℝ) ^ ((259 : ℝ) / 800) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have h5 : (x : ℝ) ^ ((5 : ℝ) / 16) ≤ (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by
      rw [← hchain]
      calc (x : ℝ) ^ ((5 : ℝ) / 16) = (1 / 4) * (4 * (x : ℝ) ^ ((5 : ℝ) / 16)) := by ring
        _ ≤ (1 / 4) * ((x : ℝ) ^ ((9 : ℝ) / 800) * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx4 hA5) (by norm_num)
        _ = (1 / 4) * ((x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((9 : ℝ) / 800)) := by ring
    exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt hx1 hlt5) h5
  linarith

private lemma RangeC2 (B : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      s1 x * (Real.exp 1 * Y1 x) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) := by
  have hb0 := FI_ev_mul_rpow_log_rpow_lt_nat (a := (49 : ℝ) / 100) (b := B) (c := (1 : ℝ) / 2)
    (C := Real.exp 1 / 2) (by positivity) (by norm_num)
  filter_upwards [FI_ev_s1_le_two_W1, FI_ev_W1_upper, FI_ev_Y1_upper, FI_ev_ge_one,
    FI_ev_log_ge_nat 1, hb0] with x hs1 hWu hYu hx1 hlog hb
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hLpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hLpow : 0 < (Real.log (x : ℝ)) ^ B := Real.rpow_pos_of_pos hLpos B
  have hlogneg : (Real.log (x : ℝ)) ^ (-B) = ((Real.log (x : ℝ)) ^ B)⁻¹ :=
    Real.rpow_neg (le_of_lt hLpos) B
  have hYnn : 0 ≤ Y1 x := FI_Y1_nonneg x
  have hprod : W1 x * Y1 x ≤ (1 / 4) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    have h := mul_le_mul hWu hYu hYnn (by positivity)
    have halg : (1 / 4) * (x : ℝ) ^ ((5 : ℝ) / 32) * (x : ℝ) ^ ((267 : ℝ) / 800)
        = (1 / 4) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
      rw [mul_assoc, ← Real.rpow_add hxpos]
      congr 1
      norm_num
    rwa [halg] at h
  have hupper : s1 x * (Real.exp 1 * Y1 x)
      ≤ (Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    have hstep : s1 x * Y1 x ≤ 2 * (W1 x * Y1 x) := by
      have h := mul_le_mul_of_nonneg_right hs1 hYnn
      have h2 : (2 * W1 x) * Y1 x = 2 * (W1 x * Y1 x) := by ring
      rwa [h2] at h
    calc s1 x * (Real.exp 1 * Y1 x) = Real.exp 1 * (s1 x * Y1 x) := by ring
      _ ≤ Real.exp 1 * (2 * (W1 x * Y1 x)) :=
            mul_le_mul_of_nonneg_left hstep (Real.exp_pos 1).le
      _ ≤ Real.exp 1 * (2 * ((1 / 4) * (x : ℝ) ^ ((49 : ℝ) / 100))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by norm_num))
              (Real.exp_pos 1).le
      _ = (Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100) := by ring
  have hmain : (Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100)
      < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) := by
    rw [hlogneg, ← div_eq_mul_inv]
    rw [lt_div_iff₀ hLpow]
    exact hb
  linarith

private lemma RangeC3 :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pcut x : ℝ) ∧
      Real.log (Pcut x : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) := by
  have h2 := FI_ev_loglog_rpow_le_nat (b := ((2 : ℕ) : ℝ)) (ε := (1 : ℝ)) (C := (1 : ℝ) / 4)
    (by norm_num) (by norm_num)
  have h4 := FI_ev_loglog_rpow_le_nat (b := ((4 : ℕ) : ℝ)) (ε := (1 : ℝ)) (C := (1 : ℝ) / 4)
    (by norm_num) (by norm_num)
  have hlog2 := FI_ev_log_ge_nat (Real.exp 1)
  filter_upwards [h2, h4, hlog2] with x h2x h4x hlogx
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) :=
    le_trans (Real.one_le_exp (by norm_num)) hlogx
  have hxpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlogx
    rwa [Real.log_exp] at h
  have hLLnn : 0 ≤ Real.log (Real.log (x : ℝ)) := le_trans zero_le_one hLL1
  have hL2 : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ (1 / 4) * Real.log (x : ℝ) := by
    rw [Real.rpow_one] at h2x
    rwa [Real.rpow_natCast] at h2x
  have hL4 : (Real.log (Real.log (x : ℝ))) ^ 4 ≤ (1 / 4) * Real.log (x : ℝ) := by
    rw [Real.rpow_one] at h4x
    rwa [Real.rpow_natCast] at h4x
  have hlogtwo : Real.log 2 ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := by
    have h2' : Real.log 2 ≤ (1 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hp : (1 : ℝ) ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := one_le_pow₀ hLL1
    linarith [hp, h2']
  have hL2nn : 0 ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := sq_nonneg _
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hL2pos : 0 < (Real.log (Real.log (x : ℝ))) ^ 2 := lt_of_lt_of_le hlog2pos hlogtwo
  have hzinv : (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ)
      = ((Real.log (Real.log (x : ℝ))) ^ 2)⁻¹ := by
    rw [← Real.rpow_intCast, show ((-2 : ℤ) : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one hLL1))]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmult : (Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2)
      * (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (x : ℝ) := by
    have hbridge : (Real.log (Real.log (x : ℝ))) ^ 2 * (Real.log (Real.log (x : ℝ))) ^ 2
        = (Real.log (Real.log (x : ℝ))) ^ 4 := by ring
    have h1 : Real.log 2 * (Real.log (Real.log (x : ℝ))) ^ 2
        ≤ (Real.log (Real.log (x : ℝ))) ^ 4 := by
      rw [← hbridge]
      exact mul_le_mul_of_nonneg_right hlogtwo hL2nn
    have h2' : (Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2)
        * (Real.log (Real.log (x : ℝ))) ^ 2
        = Real.log 2 * (Real.log (Real.log (x : ℝ))) ^ 2
          + (Real.log (Real.log (x : ℝ))) ^ 4 := by
      rw [add_mul, hbridge]
    have hlogxnn : 0 ≤ Real.log (x : ℝ) := le_of_lt hxpos
    rw [h2']
    linarith only [h1, hL4, hlogxnn]
  refine ⟨FI_log_Pcut_ge x, ?_⟩
  rw [hzinv, ← div_eq_mul_inv, le_div_iff₀ hL2pos]
  calc Real.log (Pcut x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ 2
      ≤ (Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2)
          * (Real.log (Real.log (x : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_right (FI_log_Pcut_le x) hL2nn
    _ ≤ Real.log (x : ℝ) := hmult

private lemma RangeC4 :
    ∀ᶠ x : ℕ in atTop,
      (Delta1 x : ℝ) ^ 2 ≤ (⌊Y1 x⌋₊ : ℝ) ∧ (Delta1 x : ℝ) ^ 4 ≤ (⌊Y1 x⌋₊ : ℝ) := by
  filter_upwards [FI_ev_Delta1_le_two_Lam1, FI_ev_floor_Y1_lower, FI_ev_ge_one,
      FI_ev_rpow_ge_nat ((251 : ℝ) / 800) (by norm_num) 16,
      FI_ev_rpow_ge_nat ((235 : ℝ) / 800) (by norm_num) 64]
    with x hD hfl hx1 hx16 hx64
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hL25 : (2 * Lam1 x) ^ 2 = 4 * (x : ℝ) ^ ((1 : ℝ) / 50) := by
    rw [Lam1, mul_pow]
    have h : ((x : ℝ) ^ ((1 : ℝ) / 100)) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
      congr 1
      norm_num
    rw [h]
    norm_num
  have hsq : (Delta1 x : ℝ) ^ 2 ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 50) := by
    rw [pow_two]
    have h := mul_self_le_mul_self (Nat.cast_nonneg (Delta1 x)) hD
    have h2 : (2 * Lam1 x) * (2 * Lam1 x) = 4 * (x : ℝ) ^ ((1 : ℝ) / 50) := by
      rw [← pow_two, hL25]
    linarith [h, h2]
  have hkey2 : 4 * (x : ℝ) ^ ((1 : ℝ) / 50) ≤ (x : ℝ) ^ ((267 : ℝ) / 800) / 4 := by
    have hsplit : (x : ℝ) ^ ((267 : ℝ) / 800)
        = (x : ℝ) ^ ((251 : ℝ) / 800) * (x : ℝ) ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rw [hsplit]
    have hA : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 50) := Real.rpow_nonneg (le_of_lt hxpos) _
    have h := mul_le_mul_of_nonneg_left hx16 hA
    linarith [h]
  have h4 : (Delta1 x : ℝ) ^ 4 ≤ 16 * (x : ℝ) ^ ((1 : ℝ) / 25) := by
    have h := mul_self_le_mul_self (sq_nonneg (Delta1 x : ℝ)) hsq
    have h2 : (4 * (x : ℝ) ^ ((1 : ℝ) / 50)) * (4 * (x : ℝ) ^ ((1 : ℝ) / 50))
        = 16 * (x : ℝ) ^ ((1 : ℝ) / 25) := by
      rw [← pow_two, mul_pow]
      have hh : ((x : ℝ) ^ ((1 : ℝ) / 50)) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 25) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
        congr 1
        norm_num
      rw [hh]
      norm_num
    have heq : (Delta1 x : ℝ) ^ 4 = ((Delta1 x : ℝ) ^ 2) ^ 2 := by ring
    rw [heq]
    linarith [h, h2]
  have hkey4 : 16 * (x : ℝ) ^ ((1 : ℝ) / 25) ≤ (x : ℝ) ^ ((267 : ℝ) / 800) / 4 := by
    have hsplit : (x : ℝ) ^ ((267 : ℝ) / 800)
        = (x : ℝ) ^ ((235 : ℝ) / 800) * (x : ℝ) ^ ((1 : ℝ) / 25) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rw [hsplit]
    have hA : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 25) := Real.rpow_nonneg (le_of_lt hxpos) _
    have h := mul_le_mul_of_nonneg_left hx64 hA
    linarith [h]
  exact ⟨le_trans hsq (le_trans hkey2 hfl), le_trans h4 (le_trans hkey4 hfl)⟩

private lemma RangeC5 :
    ∀ᶠ x : ℕ in atTop,
      (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ (Dcut x : ℝ) ∧
      (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) * (Pcut x : ℝ) ≤ (Dcut x : ℝ) := by
  filter_upwards [FI_ev_Delta1_le_two_Lam1, FI_ev_floor_eY1_upper, FI_ev_Dcut_lower,
      FI_ev_Pcut_le_rpow,
      FI_ev_rpow_ge_nat ((11 : ℝ) / 32) (by norm_num) (4 * Real.exp 1),
      FI_ev_rpow_ge_nat ((11 : ℝ) / 64) (by norm_num) (4 * Real.exp 1),
      FI_ev_ge_one]
    with x hD hfl hDcut hPc hx1 hx2 hxge1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hxge1
  have hfl0 : 0 ≤ (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hP0 : 0 ≤ (Pcut x : ℝ) := Nat.cast_nonneg _
  have hA1 : (Delta1 x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    have := hD
    rwa [Lam1] at this
  have hprod1 : (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ)
      ≤ 2 * Real.exp 1 * (x : ℝ) ^ ((11 : ℝ) / 32) := by
    have h := mul_le_mul hA1 hfl hfl0 (by positivity)
    have halg : 2 * (x : ℝ) ^ ((1 : ℝ) / 100) * (Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800))
        = 2 * Real.exp 1 * (x : ℝ) ^ ((11 : ℝ) / 32) := by
      rw [show 2 * (x : ℝ) ^ ((1 : ℝ) / 100) * (Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800))
            = 2 * Real.exp 1 * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((267 : ℝ) / 800)) by ring]
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rwa [halg] at h
  have hmain1 : (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ (Dcut x : ℝ) := by
    have hA : 0 ≤ (x : ℝ) ^ ((11 : ℝ) / 32) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hsq : (x : ℝ) ^ ((11 : ℝ) / 16) = (x : ℝ) ^ ((11 : ℝ) / 32) * (x : ℝ) ^ ((11 : ℝ) / 32) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have h1 : (4 * Real.exp 1) * (x : ℝ) ^ ((11 : ℝ) / 32)
        ≤ (x : ℝ) ^ ((11 : ℝ) / 32) * (x : ℝ) ^ ((11 : ℝ) / 32) :=
      mul_le_mul_of_nonneg_right hx1 hA
    have h2 : 2 * Real.exp 1 * (x : ℝ) ^ ((11 : ℝ) / 32) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
      rw [hsq]
      linarith [h1]
    linarith [hprod1, h2, hDcut]
  have hprod2 : (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) * (Pcut x : ℝ)
      ≤ 2 * Real.exp 1 * (x : ℝ) ^ ((33 : ℝ) / 64) := by
    have h := mul_le_mul hprod1 hPc hP0 (by positivity)
    have halg : 2 * Real.exp 1 * (x : ℝ) ^ ((11 : ℝ) / 32) * (x : ℝ) ^ ((11 : ℝ) / 64)
        = 2 * Real.exp 1 * (x : ℝ) ^ ((33 : ℝ) / 64) := by
      rw [show 2 * Real.exp 1 * (x : ℝ) ^ ((11 : ℝ) / 32) * (x : ℝ) ^ ((11 : ℝ) / 64)
            = 2 * Real.exp 1 * ((x : ℝ) ^ ((11 : ℝ) / 32) * (x : ℝ) ^ ((11 : ℝ) / 64)) by ring]
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rwa [halg] at h
  have hmain2 : (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) * (Pcut x : ℝ) ≤ (Dcut x : ℝ) := by
    have hA : 0 ≤ (x : ℝ) ^ ((33 : ℝ) / 64) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hsplit : (x : ℝ) ^ ((11 : ℝ) / 16)
        = (x : ℝ) ^ ((33 : ℝ) / 64) * (x : ℝ) ^ ((11 : ℝ) / 64) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have h1 : (x : ℝ) ^ ((33 : ℝ) / 64) * (4 * Real.exp 1)
        ≤ (x : ℝ) ^ ((33 : ℝ) / 64) * (x : ℝ) ^ ((11 : ℝ) / 64) :=
      mul_le_mul_of_nonneg_left hx2 hA
    have h2 : 2 * Real.exp 1 * (x : ℝ) ^ ((33 : ℝ) / 64) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
      rw [hsplit]
      linarith [h1]
    linarith [hprod2, h2, hDcut]
  exact ⟨hmain1, hmain2⟩

private lemma RangeC6 :
    ∀ᶠ x : ℕ in atTop, (Delta1 x : ℝ) < s1 x * z1 x := by
  filter_upwards [FI_ev_W1_lower, FI_ev_W1_le_s1, FI_ev_Y1_lower, FI_ev_Delta1_le_two_Lam1,
    FI_ev_rpow_ge_nat ((47 : ℝ) / 100) (by norm_num) 33, FI_ev_ge_one]
    with x hWl hs1W hYl hD hx32 hx1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hYnn : 0 ≤ Y1 x := FI_Y1_nonneg x
  have hstep : (1 / 8) * (x : ℝ) ^ ((117 : ℝ) / 800) * ((x : ℝ) ^ ((267 : ℝ) / 800) / 2)
      ≤ s1 x * z1 x := by
    have h1 : W1 x * Y1 x ≤ s1 x * z1 x := by
      rw [z1]
      exact mul_le_mul_of_nonneg_right hs1W hYnn
    have h2 : (1 / 8) * (x : ℝ) ^ ((117 : ℝ) / 800) * ((x : ℝ) ^ ((267 : ℝ) / 800) / 2)
        ≤ W1 x * Y1 x :=
      mul_le_mul hWl hYl (by positivity) (FI_W1_nonneg x)
    linarith
  have halg : (1 / 8) * (x : ℝ) ^ ((117 : ℝ) / 800) * ((x : ℝ) ^ ((267 : ℝ) / 800) / 2)
      = (1 / 16) * (x : ℝ) ^ ((12 : ℝ) / 25) := by
    rw [show (1 / 8) * (x : ℝ) ^ ((117 : ℝ) / 800) * ((x : ℝ) ^ ((267 : ℝ) / 800) / 2)
          = (1 / 16) * ((x : ℝ) ^ ((117 : ℝ) / 800) * (x : ℝ) ^ ((267 : ℝ) / 800)) by ring]
    rw [← Real.rpow_add hxpos]
    congr 1
    norm_num
  have hmain : (Delta1 x : ℝ) < (1 / 16) * (x : ℝ) ^ ((12 : ℝ) / 25) := by
    have hA1 : (Delta1 x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
      have := hD
      rwa [Lam1] at this
    have h2 : (1 / 16) * (x : ℝ) ^ ((12 : ℝ) / 25)
        = (1 / 16) * (x : ℝ) ^ ((47 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100) := by
      rw [show (1 / 16) * (x : ℝ) ^ ((47 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100)
            = (1 / 16) * ((x : ℝ) ^ ((47 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100)) by ring]
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have h3 : 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
        < (1 / 16) * (x : ℝ) ^ ((47 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100) := by
      have hApos : 0 < (x : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
      have hb : 32 * (x : ℝ) ^ ((1 : ℝ) / 100)
          < (x : ℝ) ^ ((47 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100) :=
        mul_lt_mul_of_pos_right (by linarith : (32 : ℝ) < (x : ℝ) ^ ((47 : ℝ) / 100)) hApos
      linarith [hb]
    rw [h2]
    linarith [hA1, h3]
  rw [halg] at hstep
  linarith [hstep, hmain]

private lemma RangeC7 :
    ∀ᶠ x : ℕ in atTop,
      (Delta1 x : ℝ) * (Mcutb x : ℝ) * (d2b x : ℝ) ≤ (Dcut x : ℝ) := by
  have hb0 := FI_ev_mul_rpow_log_rpow_lt_nat (a := (54 : ℝ) / 100) (b := ((6 : ℕ) : ℝ))
    (c := (11 : ℝ) / 16) (C := 2340) (by norm_num) (by norm_num)
  filter_upwards [FI_ev_Delta1_le_two_Lam1, FI_ev_Mcutb_le, FI_ev_d2b_le, FI_ev_Dcut_lower,
    FI_ev_ge_one, hb0] with x hD hM hd hDcut hx1 hb
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hd0 : 0 ≤ (d2b x : ℝ) := Nat.cast_nonneg _
  have hA1 : (Delta1 x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    have := hD
    rwa [Lam1] at this
  have hA2 : (Mcutb x : ℝ) ≤ 9 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2 := by
    have heq : 9 * Lam1 x * del1 x * Real.sqrt (x : ℝ)
        = 9 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2 := by
      rw [Lam1, del1, Real.sqrt_eq_rpow]
      rw [show 9 * (x : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2 * (x : ℝ) ^ ((1 : ℝ) / 2)
            = 9 * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 2))
              * (Real.log (x : ℝ)) ^ 2 by ring]
      rw [← Real.rpow_add hxpos, show ((1 : ℝ) / 100 + (1 : ℝ) / 2) = (51 : ℝ) / 100 by norm_num]
    rwa [heq] at hM
  have hA3 : (d2b x : ℝ) ≤ 65 * (x : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 4 := by
    have heq : 65 * (Lam1 x) ^ 2 * (del1 x) ^ 2
        = 65 * (x : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 4 := by
      rw [Lam1, del1]
      have h1 : ((x : ℝ) ^ ((1 : ℝ) / 100)) ^ 2 = (x : ℝ) ^ ((2 : ℝ) / 100) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
        congr 1
        norm_num
      have h2 : ((Real.log (x : ℝ)) ^ 2) ^ 2 = (Real.log (x : ℝ)) ^ 4 := by ring
      rw [h1, h2]
    rwa [heq] at hd
  have hprod : (Delta1 x : ℝ) * (Mcutb x : ℝ) * (d2b x : ℝ)
      ≤ 1170 * (x : ℝ) ^ ((54 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 6 := by
    have h01 : (Delta1 x : ℝ) * (Mcutb x : ℝ)
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
            * (9 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2) :=
      mul_le_mul hA1 hA2 (Nat.cast_nonneg _) (by positivity)
    have h02 : (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
          * (9 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2)
        = 18 * (x : ℝ) ^ ((52 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2 := by
      rw [show 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
              * (9 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2)
            = 18 * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((51 : ℝ) / 100))
              * (Real.log (x : ℝ)) ^ 2 by ring]
      rw [← Real.rpow_add hxpos, show ((1 : ℝ) / 100 + (51 : ℝ) / 100) = (52 : ℝ) / 100 by norm_num]
    have h03 : (Delta1 x : ℝ) * (Mcutb x : ℝ)
        ≤ 18 * (x : ℝ) ^ ((52 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2 := by
      rwa [h02] at h01
    have h12 : (Delta1 x : ℝ) * (Mcutb x : ℝ) * (d2b x : ℝ)
        ≤ (18 * (x : ℝ) ^ ((52 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2)
            * (65 * (x : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 4) :=
      mul_le_mul h03 hA3 hd0 (by positivity)
    have h12' : (18 * (x : ℝ) ^ ((52 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2)
          * (65 * (x : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 4)
        = 1170 * (x : ℝ) ^ ((54 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 6 := by
      rw [show (18 * (x : ℝ) ^ ((52 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 2)
              * (65 * (x : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 4)
            = 1170 * ((x : ℝ) ^ ((52 : ℝ) / 100) * (x : ℝ) ^ ((2 : ℝ) / 100))
              * ((Real.log (x : ℝ)) ^ 2 * (Real.log (x : ℝ)) ^ 4) by ring]
      rw [← Real.rpow_add hxpos, show ((52 : ℝ) / 100 + (2 : ℝ) / 100) = (54 : ℝ) / 100 by norm_num,
        ← pow_add]
    linarith [h12, h12']
  rw [Real.rpow_natCast] at hb
  have hb2 : 1170 * (x : ℝ) ^ ((54 : ℝ) / 100) * (Real.log (x : ℝ)) ^ 6
      < (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by linarith [hb]
  linarith [hprod, hb2, hDcut]

private lemma RangeC8 :
    ∀ᶠ x : ℕ in atTop,
      ⌊Real.exp 1 * Y1 x⌋₊ ≤ x ∧ Real.log (x : ℝ) ≤ 4 * Real.log (⌊Y1 x⌋₊ : ℝ) := by
  filter_upwards [FI_ev_floor_eY1_upper, FI_ev_floor_Y1_lower, FI_ev_ge_one,
    FI_ev_rpow_ge_nat ((533 : ℝ) / 800) (by norm_num) (Real.exp 1),
    FI_ev_rpow_ge_nat ((267 : ℝ) / 800) (by norm_num) 4,
    FI_ev_log_ge_nat (800 * Real.log 4 / 67)]
    with x hfl hYl hx1 hxexp hx4 hxlog
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hA267 : 0 ≤ (x : ℝ) ^ ((267 : ℝ) / 800) := Real.rpow_nonneg (le_of_lt hxpos) _
  refine ⟨?_, ?_⟩
  · have hsplit : (x : ℝ) ^ ((533 : ℝ) / 800) * (x : ℝ) ^ ((267 : ℝ) / 800)
        = (x : ℝ) ^ ((800 : ℝ) / 800) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    have hxone : (x : ℝ) ^ ((800 : ℝ) / 800) = (x : ℝ) := by
      rw [show (800 : ℝ) / 800 = 1 by norm_num, Real.rpow_one]
    have h1 : Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800) ≤ (x : ℝ) :=
      calc Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800)
          ≤ (x : ℝ) ^ ((533 : ℝ) / 800) * (x : ℝ) ^ ((267 : ℝ) / 800) :=
            mul_le_mul_of_nonneg_right hxexp hA267
        _ = (x : ℝ) ^ ((800 : ℝ) / 800) := hsplit
        _ = (x : ℝ) := hxone
    have h2 : (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ (x : ℝ) := le_trans hfl h1
    exact_mod_cast h2
  · have hYpos : 0 < (⌊Y1 x⌋₊ : ℝ) := by
      have h4 : (1 : ℝ) ≤ (x : ℝ) ^ ((267 : ℝ) / 800) / 4 := by linarith [hx4]
      linarith [hYl, h4]
    have hApos : 0 < (x : ℝ) ^ ((267 : ℝ) / 800) / 4 := by linarith [hx4, hA267]
    have hloglow : Real.log ((x : ℝ) ^ ((267 : ℝ) / 800) / 4) ≤ Real.log (⌊Y1 x⌋₊ : ℝ) :=
      Real.log_le_log hApos hYl
    have hsplit : Real.log ((x : ℝ) ^ ((267 : ℝ) / 800) / 4)
        = (267 : ℝ) / 800 * Real.log (x : ℝ) - Real.log 4 := by
      have hA : (0 : ℝ) < (x : ℝ) ^ ((267 : ℝ) / 800) := Real.rpow_pos_of_pos hxpos _
      rw [div_eq_mul_inv, Real.log_mul (ne_of_gt hA) (by norm_num : ((4 : ℝ))⁻¹ ≠ 0),
        Real.log_inv, Real.log_rpow hxpos]
      ring
    have hmain : (1 / 4) * Real.log (x : ℝ) ≤ Real.log (⌊Y1 x⌋₊ : ℝ) := by
      have hle : (1 / 4) * Real.log (x : ℝ)
          ≤ (267 : ℝ) / 800 * Real.log (x : ℝ) - Real.log 4 := by linarith [hxlog]
      rw [← hsplit] at hle
      linarith [hloglow, hle]
    linarith [hmain]

private lemma RangeC9 :
    ∀ᶠ x : ℕ in atTop, (2 : ℝ) ≤ del1 x ∧ Real.log (Delta1 x : ℝ) ≤ Real.log (x : ℝ) := by
  filter_upwards [FI_ev_log_ge_nat (Real.sqrt 2), FI_ev_Lam1_ge_one, FI_ev_Delta1_le_two_Lam1,
    FI_ev_ge_one, FI_ev_rpow_ge_nat ((99 : ℝ) / 100) (by norm_num) 2]
    with x hlg hLam hD hx1 hx99
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hdel : (2 : ℝ) ≤ del1 x := by
    rw [del1]
    have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : Real.sqrt 2 * Real.sqrt 2 ≤ Real.log (x : ℝ) * Real.log (x : ℝ) :=
      mul_le_mul hlg hlg hs (le_trans hs hlg)
    rw [← pow_two] at h1
    linarith [h1, hs2]
  have hA1 : (Delta1 x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    have := hD
    rwa [Lam1] at this
  have hDelta_le : (Delta1 x : ℝ) ≤ (x : ℝ) := by
    have hsplit : (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((99 : ℝ) / 100) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    rw [hsplit]
    have hApos : 0 < (x : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
    have h := mul_le_mul_of_nonneg_left hx99 (le_of_lt hApos)
    linarith [h, hA1]
  have hDpos : 0 < (Delta1 x : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_trans hLam (FI_Lam1_le_Delta1 x))
  exact ⟨hdel, Real.log_le_log hDpos hDelta_le⟩

/-! ## The assembled range check -/

theorem RangeCheckChain (η B : ℝ) (hη : 0 < η) (hη2 : η < 1 / 16) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < Y1 x / (Delta1 x : ℝ) ∧
      s1 x * (Real.exp 1 * Y1 x) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) ∧
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pcut x : ℝ) ∧
      Real.log (Pcut x : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) ∧
      (Delta1 x : ℝ) ^ 2 ≤ (⌊Y1 x⌋₊ : ℝ) ∧
      (Delta1 x : ℝ) ^ 4 ≤ (⌊Y1 x⌋₊ : ℝ) ∧
      (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ (Dcut x : ℝ) ∧
      (Delta1 x : ℝ) * (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) * (Pcut x : ℝ) ≤ (Dcut x : ℝ) ∧
      (Delta1 x : ℝ) < s1 x * z1 x ∧
      (Delta1 x : ℝ) * (Mcutb x : ℝ) * (d2b x : ℝ) ≤ (Dcut x : ℝ) ∧
      ⌊Real.exp 1 * Y1 x⌋₊ ≤ x ∧
      Real.log (x : ℝ) ≤ 4 * Real.log (⌊Y1 x⌋₊ : ℝ) ∧
      (2 : ℝ) ≤ del1 x ∧
      Real.log (Delta1 x : ℝ) ≤ Real.log (x : ℝ) := by
  filter_upwards [RangeC1 η hη2, RangeC2 B, RangeC3, RangeC4, RangeC5, RangeC6, RangeC7,
    RangeC8, RangeC9] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6, h7, h8.1, h8.2, h9.1, h9.2⟩

end

end Work.FITop
