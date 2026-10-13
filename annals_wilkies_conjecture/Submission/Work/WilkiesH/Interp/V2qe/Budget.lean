import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.V2qb.Qval
import Submission.Work.WilkiesH.Interp.V2qb.q_bound_b_succ
import Submission.Work.WilkiesH.Interp.V2qe._aux

/-!
# The five budget inequalities

Each of the five summands produced by expanding `log (1/ε)` is bounded by `qval μ D g H`
(with a factor `8` to spare), by the shrinking estimate `qval_rpow_key`, the `d ≤ _ `
estimate `dV_le_qval_rpow_aux`, and elementary constant comparisons.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qe

open Work.WilkiesH.Interp V2qb

/-- `8·(4 + (d+1) + (μ+1)) ≤ qval`. -/
lemma budget_A (μ D g H : ℕ) (hH : 1 ≤ H)
    (hdM : ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤
      408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) :
    8 * (4 + (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) + ((μ:ℝ)+1)) ≤ qval μ D g H := by
  have hMpos : 0 < qval μ D g H := qval_pos μ D g H hH
  have hxd : (0:ℝ) ≤ (μ:ℝ) := nat_cast_nonneg_R μ
  have hrg : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith
  -- constant part
  have h64 : (16:ℝ) * ((μ:ℝ)+6) ≤ (2:ℝ)^60 * ((μ:ℝ)+2) := by
    have h1 : (16:ℝ) * ((μ:ℝ)+6) ≤ (16:ℝ) * (4*((μ:ℝ)+2)) :=
      mul_le_mul_of_nonneg_left (by linarith : (μ:ℝ)+6 ≤ 4*((μ:ℝ)+2)) (by norm_num)
    have h2 : (16:ℝ) * (4*((μ:ℝ)+2)) = 64*((μ:ℝ)+2) := by ring
    have h3 : (64:ℝ) ≤ (2:ℝ)^60 := by norm_num
    have h4 : (64:ℝ) * ((μ:ℝ)+2) ≤ (2:ℝ)^60 * ((μ:ℝ)+2) :=
      mul_le_mul_of_nonneg_right h3 hrg
    linarith [h1, h2.le, h2.ge, h4]
  have hc : 8 * (4 + 1 + ((μ:ℝ)+1)) ≤ qval μ D g H / 2 := by
    have hrw : 8 * (4 + 1 + ((μ:ℝ)+1)) = 8 * ((μ:ℝ)+6) := by ring
    rw [hrw]
    have h16 : (16:ℝ) * ((μ:ℝ)+6) ≤ qval μ D g H :=
      le_trans h64 (le_trans (CCc_ge_two_pow_mul μ) (qval_ge_CCc μ D g H))
    linarith
  -- the `d` part
  have hd1 : (1:ℝ) ≤ ((dV μ g (bV μ g H) : ℕ) : ℝ) := by
    exact_mod_cast one_le_dV μ g (bV μ g H)
  have hkey : 13056 * ((μ:ℝ)+1) * (1+(g:ℝ)) ≤ (qval μ D g H)^(1/((μ:ℝ)+1)) := by
    have h := qval_rpow_key μ D g H (C := 13056 * ((μ:ℝ)+1)) (k := 1) (m := 0)
      (mul_nonneg (by norm_num) (by linarith))
      (le_pow_mu μ (by
        have h1 : (0:ℝ) ≤ (g:ℝ) := nat_cast_nonneg_R g
        have h2 : (13056:ℝ) ≤ (2:ℝ)^60 := by norm_num
        have h3 : ((μ:ℝ)+1) ≤ ((μ:ℝ)+2)^2 := by nlinarith [hxd, hrg]
        calc (13056:ℝ) * ((μ:ℝ)+1) ≤ (2:ℝ)^60 * ((μ:ℝ)+1) :=
              mul_le_mul_of_nonneg_right h2 (by linarith)
          _ ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2 := mul_le_mul_of_nonneg_left h3 (by positivity)))
      (one_le_thousand_cube μ) (Nat.zero_le _)
    simpa using h
  have h32 : 32 * ((dV μ g (bV μ g H) : ℕ) : ℝ)
      ≤ 32 * (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) :=
    mul_le_mul_of_nonneg_left hdM (by norm_num)
  have h16d : 16 * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) ≤ qval μ D g H := by
    have hstep : 16 * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) ≤
        16 * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ)) := by linarith
    calc 16 * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)
        ≤ 16 * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ)) := hstep
      _ = 32 * ((dV μ g (bV μ g H) : ℕ) : ℝ) := by ring
      _ ≤ 32 * (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) := h32
      _ = (13056 * ((μ:ℝ)+1) * (1+(g:ℝ))) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by ring
      _ ≤ qval μ D g H := const_rpow_mul_le μ (qval μ D g H) hMpos _ hkey
  linarith [hc, h16d]

/-- `8·(2(1+g)((μ+1)(d+1))) ≤ qval`. -/
lemma budget_B (μ D g H : ℕ) (hH : 1 ≤ H)
    (hdM : ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤
      408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) :
    8 * (2 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1))) ≤ qval μ D g H := by
  have hMpos : 0 < qval μ D g H := qval_pos μ D g H hH
  have hxd : (0:ℝ) ≤ (μ:ℝ) := nat_cast_nonneg_R μ
  have hxk : (0:ℝ) ≤ (μ:ℝ)+1 := by linarith
  have hxk2 : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith
  have hg0 : (0:ℝ) ≤ (g:ℝ) := nat_cast_nonneg_R g
  have hg1 : (0:ℝ) ≤ 1+(g:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ ((dV μ g (bV μ g H) : ℕ) : ℝ) := by
    exact_mod_cast one_le_dV μ g (bV μ g H)
  have hkey : 13056 * ((μ:ℝ)+1)^2 * (1+(g:ℝ))^2 ≤ (qval μ D g H)^(1/((μ:ℝ)+1)) := by
    have h := qval_rpow_key μ D g H (C := 13056 * ((μ:ℝ)+1)^2) (k := 2) (m := 0)
      (mul_nonneg (by norm_num) (pow_nonneg hxk 2))
      (le_pow_mu μ (by
        have h2 : (13056:ℝ) ≤ (2:ℝ)^60 := by norm_num
        have h3 : ((μ:ℝ)+1)^2 ≤ ((μ:ℝ)+2)^2 := by nlinarith [hxd]
        calc (13056:ℝ) * ((μ:ℝ)+1)^2 ≤ (2:ℝ)^60 * ((μ:ℝ)+1)^2 :=
              mul_le_mul_of_nonneg_right h2 (pow_nonneg hxk 2)
          _ ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2 := mul_le_mul_of_nonneg_left h3 (by positivity)))
      (two_le_thousand_cube μ) (Nat.zero_le _)
    simpa using h
  have hfin : 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1))
      ≤ (13056 * ((μ:ℝ)+1)^2 * (1+(g:ℝ))^2) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by
    have h1 : (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) ≤ 2 * ((dV μ g (bV μ g H) : ℕ) : ℝ) := by
      linarith
    have h2 : ((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)
        ≤ ((μ:ℝ)+1) * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hxk
    have h3 : 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1))
        ≤ 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ)))
        = 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1)) * ((dV μ g (bV μ g H) : ℕ) : ℝ) := by ring
    have h5 : 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1)) * ((dV μ g (bV μ g H) : ℕ) : ℝ)
        ≤ 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1))
            * (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hdM (by positivity)
    have h6 : 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1))
            * (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)))
        = (13056 * ((μ:ℝ)+1)^2 * (1+(g:ℝ))^2) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by ring
    calc 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1))
        ≤ 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (2 * ((dV μ g (bV μ g H) : ℕ) : ℝ))) := h3
      _ = 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1)) * ((dV μ g (bV μ g H) : ℕ) : ℝ) := h4
      _ ≤ 32 * ((1+(g:ℝ)) * ((μ:ℝ)+1))
            * (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) := h5
      _ = (13056 * ((μ:ℝ)+1)^2 * (1+(g:ℝ))^2) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := h6
  have hrw : 8 * (2 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)))
      = 16 * (1+(g:ℝ)) * (((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)) := by ring
  rw [hrw]
  exact le_trans hfin (const_rpow_mul_le μ (qval μ D g H) hMpos _ hkey)

/-- `8·(16(1+g)) ≤ qval`. -/
lemma budget_C (μ D g H : ℕ) (hH : 1 ≤ H) :
    8 * (16 * (1+(g:ℝ))) ≤ qval μ D g H := by
  have hmain := qval_ge_main μ D g H
  have hCC0 : (0:ℝ) ≤ (CCc μ : ℝ) := nat_cast_nonneg_R _
  have hg0 : (0:ℝ) ≤ (g:ℝ) := nat_cast_nonneg_R g
  have hg1 : (1:ℝ) ≤ 1 + (g:ℝ) := one_le_one_add_g g
  have hcc : (128:ℝ) ≤ (CCc μ : ℝ) := by
    have h := CCc_ge_two_pow_mul μ
    have hx : (1:ℝ) ≤ (μ:ℝ)+2 := by linarith [nat_cast_nonneg_R μ]
    have h1 : (128:ℝ) ≤ (2:ℝ)^60 := by norm_num
    have h2 : (128:ℝ) ≤ (2:ℝ)^60 * ((μ:ℝ)+2) := by
      calc (128:ℝ) ≤ (2:ℝ)^60 := h1
        _ = (2:ℝ)^60 * 1 := by ring
        _ ≤ (2:ℝ)^60 * ((μ:ℝ)+2) := mul_le_mul_of_nonneg_left hx (by positivity)
    linarith [h, h2]
  have hgp : (1+(g:ℝ)) ≤ (1+(g:ℝ))^(Ec μ) := by
    simpa using pow_le_pow_right₀ hg1 (one_le_Ec μ)
  have hHp : (1:ℝ) ≤ (1+Real.log H)^(Fc μ) := one_le_pow₀ (one_le_one_add_log H)
  have h1 : 128 * (1+(g:ℝ)) ≤ (CCc μ : ℝ) * (1+(g:ℝ)) :=
    mul_le_mul_of_nonneg_right hcc (by linarith)
  have h2 : (CCc μ : ℝ) * (1+(g:ℝ)) ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) :=
    mul_le_mul_of_nonneg_left hgp hCC0
  have h3 : (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ)
      ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) := by
    have hnn : (0:ℝ) ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) :=
      mul_nonneg hCC0 (pow_nonneg (by linarith) _)
    calc (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ)
        = (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * 1 := by ring
      _ ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) :=
          mul_le_mul_of_nonneg_left hHp hnn
  have h4 : 8 * (16 * (1+(g:ℝ))) = 128 * (1+(g:ℝ)) := by ring
  rw [h4]
  exact le_trans h1 (le_trans h2 (le_trans h3 hmain))

/-- `8·((1+g) b log K) ≤ qval`. -/
lemma budget_D (μ D g H : ℕ) (hH : 1 ≤ H) :
    8 * ((1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * Real.log ((KK μ : ℕ):ℝ)) ≤ qval μ D g H := by
  have hmain := qval_ge_main μ D g H
  have hlogK : 8 * Real.log ((KK μ : ℕ):ℝ) ≤ ((μ:ℝ)+2)^(60*(μ+1)^2) := log_KK_le_eight μ
  have hbVcast : ((bV μ g H : ℕ):ℝ) = (EE μ : ℝ) * (1+(g:ℝ))^(AA μ) * (((lgNat H : ℕ):ℝ))^(BB μ) := by
    simp only [bV]; push_cast; ring
  have hEE := EE_mul_pow_CCc μ
  have hg1 : (1:ℝ) ≤ 1 + (g:ℝ) := one_le_one_add_g g
  have hg0 : (0:ℝ) ≤ (g:ℝ) := nat_cast_nonneg_R g
  have hbV0 : (0:ℝ) ≤ ((bV μ g H : ℕ):ℝ) := nat_cast_nonneg_R _
  have hA : (1+(g:ℝ))^(AA μ + 1) ≤ (1+(g:ℝ))^(Ec μ) :=
    pow_le_pow_right₀ hg1 (AA_succ_le_EcV μ)
  have hL : (((lgNat H : ℕ):ℝ))^(BB μ) ≤ (1+Real.log H)^(Fc μ) := lgNat_pow_le μ H hH
  have hCC0 : (0:ℝ) ≤ (CCc μ : ℝ) := nat_cast_nonneg_R _
  have h1 : 8 * ((1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * Real.log ((KK μ : ℕ):ℝ))
      = (1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * (8 * Real.log ((KK μ : ℕ):ℝ)) := by ring
  have h2 : (1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * (8 * Real.log ((KK μ : ℕ):ℝ))
      ≤ (1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * ((μ:ℝ)+2)^(60*(μ+1)^2) := by
    have h0 : (0:ℝ) ≤ (1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) := mul_nonneg (by linarith) hbV0
    exact mul_le_mul_of_nonneg_left hlogK h0
  have h3 : (1+(g:ℝ)) * ((bV μ g H : ℕ):ℝ) * ((μ:ℝ)+2)^(60*(μ+1)^2)
      = (CCc μ : ℝ) * (1+(g:ℝ))^(AA μ + 1) * (((lgNat H : ℕ):ℝ))^(BB μ) := by
    rw [hbVcast]
    have hp : (1+(g:ℝ))^(AA μ + 1) = (1+(g:ℝ)) * (1+(g:ℝ))^(AA μ) := by rw [pow_succ']
    rw [hp]
    have hr : (1+(g:ℝ)) * ((EE μ : ℝ) * (1+(g:ℝ))^(AA μ) * (((lgNat H : ℕ):ℝ))^(BB μ))
          * ((μ:ℝ)+2)^(60*(μ+1)^2)
        = ((EE μ : ℝ) * ((μ:ℝ)+2)^(60*(μ+1)^2))
            * ((1+(g:ℝ)) * (1+(g:ℝ))^(AA μ) * (((lgNat H : ℕ):ℝ))^(BB μ)) := by ring
    rw [hr, hEE]
    ring
  have h4 : (CCc μ : ℝ) * (1+(g:ℝ))^(AA μ + 1) * (((lgNat H : ℕ):ℝ))^(BB μ)
      ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) := by
    calc (CCc μ : ℝ) * (1+(g:ℝ))^(AA μ + 1) * (((lgNat H : ℕ):ℝ))^(BB μ)
        ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (((lgNat H : ℕ):ℝ))^(BB μ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hCC0)
            (pow_nonneg (nat_cast_nonneg_R _) _)
      _ ≤ (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) :=
          mul_le_mul_of_nonneg_left hL (mul_nonneg hCC0 (pow_nonneg (by linarith) _))
  rw [h1]
  exact le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 hmain))

/-- `8·((μ+2) d g² log H) ≤ qval`. -/
lemma budget_E (μ D g H : ℕ) (hH : 1 ≤ H)
    (hdM : ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤
      408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) :
    8 * (((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ)) ≤ qval μ D g H := by
  have hMpos : 0 < qval μ D g H := qval_pos μ D g H hH
  have hM0 : (0:ℝ) ≤ qval μ D g H := le_of_lt hMpos
  have hxd : (0:ℝ) ≤ (μ:ℝ) := nat_cast_nonneg_R μ
  have hxk : (0:ℝ) ≤ (μ:ℝ)+1 := by linarith
  have hxk2 : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith
  have hg0 : (0:ℝ) ≤ (g:ℝ) := nat_cast_nonneg_R g
  have hlogH0 : (0:ℝ) ≤ Real.log (H:ℝ) := log_nat_nonneg H
  have hdM0 : (0:ℝ) ≤ ((dV μ g (bV μ g H) : ℕ) : ℝ) := nat_cast_nonneg_R _
  have hg2 : (0:ℝ) ≤ (g:ℝ)^2 := pow_nonneg hg0 2
  -- the shrinking input
  have hkey : 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ)
      ≤ (qval μ D g H)^(1/((μ:ℝ)+1)) := by
    have hC1 : (0:ℝ) ≤ 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) :=
      mul_nonneg (mul_nonneg (by norm_num) hxk2) hxk
    have hgg : (1+(g:ℝ)) * (g:ℝ)^2 ≤ (1+(g:ℝ))^3 := by nlinarith [hg0]
    have hll : Real.log (H:ℝ) ≤ 1 + Real.log (H:ℝ) := by linarith
    have hred : 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ)
        ≤ 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ))^3 * (1+Real.log (H:ℝ)) := by
      calc 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ)
          = (3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1)) * ((1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ)) := by ring
        _ ≤ (3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1)) * ((1+(g:ℝ))^3 * (1+Real.log (H:ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hC1
            exact mul_le_mul hgg hll hlogH0 (pow_nonneg (by linarith) 3)
        _ = 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ))^3 * (1+Real.log (H:ℝ)) := by ring
    have hkey0 := qval_rpow_key μ D g H (C := 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1)) (k := 3) (m := 1)
      hC1
      (le_pow_mu μ (by
        have h2 : (3264:ℝ) ≤ (2:ℝ)^60 := by norm_num
        have h3 : ((μ:ℝ)+2) * ((μ:ℝ)+1) ≤ ((μ:ℝ)+2)^2 := by nlinarith [hxd]
        have h4 : (3264:ℝ) * (((μ:ℝ)+2) * ((μ:ℝ)+1)) ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2 := by
          calc (3264:ℝ) * (((μ:ℝ)+2) * ((μ:ℝ)+1))
              ≤ (2:ℝ)^60 * (((μ:ℝ)+2) * ((μ:ℝ)+1)) :=
                mul_le_mul_of_nonneg_right h2 (mul_nonneg hxk2 hxk)
            _ ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2 := mul_le_mul_of_nonneg_left h3 (by positivity)
        have he : (3264:ℝ) * ((μ:ℝ)+2) * ((μ:ℝ)+1) = (3264:ℝ) * (((μ:ℝ)+2) * ((μ:ℝ)+1)) := by ring
        linarith [h4, he.le, he.ge]))
      (three_le_thousand_cube μ) (one_le_thousand_cube μ)
    calc 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ)
        ≤ 3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ))^3 * (1+Real.log (H:ℝ)) := hred
      _ ≤ (qval μ D g H)^(1/((μ:ℝ)+1)) := by simpa using hkey0
  -- multiply the `d` bound by `8(μ+2)g²log H`
  have hY : 8 * ((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ)
      ≤ (3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ))
          * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by
    have h0 : (0:ℝ) ≤ 8 * ((μ:ℝ)+2) * (g:ℝ)^2 * Real.log (H:ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hxk2) hg2) hlogH0
    have hmul := mul_le_mul_of_nonneg_right hdM h0
    have he : ((dV μ g (bV μ g H) : ℕ) : ℝ) * (8 * ((μ:ℝ)+2) * (g:ℝ)^2 * Real.log (H:ℝ))
        = 8 * ((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ) := by ring
    have he2 : (408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)))
          * (8 * ((μ:ℝ)+2) * (g:ℝ)^2 * Real.log (H:ℝ))
        = (3264 * ((μ:ℝ)+2) * ((μ:ℝ)+1) * (1+(g:ℝ)) * (g:ℝ)^2 * Real.log (H:ℝ))
            * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by ring
    rw [← he, ← he2]
    exact hmul
  have hrw : 8 * (((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ))
      = 8 * ((μ:ℝ)+2) * ((dV μ g (bV μ g H) : ℕ) : ℝ) * (g:ℝ)^2 * Real.log (H:ℝ) := by ring
  rw [hrw]
  exact le_trans hY (const_rpow_mul_le μ (qval μ D g H) hMpos _ hkey)

end Work.WilkiesH.Interp.V2qe
