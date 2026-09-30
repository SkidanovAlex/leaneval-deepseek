import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi
import Submission.Work.BW.num_blaschke_eta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 4000000

/-- BW §19, the `h1` half of the extrapolation step at descent level `J`: with
`S' = ⌊2^j ξ^{-rJ} S⌋`, `T' = ⌊(1-ξ) ξ^j ξ^{rJ} T⌋`, `R = 7.2 S'` and `δ = R - |s|`, the
`𝒥`-condition `log(R/δ) + U - W < -log 2` of `extrap_core` follows from the JP-arithmetic
hypothesis `hJP`.  The log-term is bounded by `log(7.2/5.19) ≤ 0.4`, the three archimedean
pieces of `U` by `num_T` (giving `dhT ≤ 0.735 SD`), the level-`J` scaled term
`1.008 (7.2S'+|s|)2^{-J}D ≤ 9.2736·2^j(2ξ^r)^{-J}SD`, and `W` by
`(2S'+1)(T'+1)(log 7.2S' - log max(|s|,S')) ≥ 16.06 (2ξ)^j SD`. -/
theorem extrap_int_h1 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : (J : ℝ) ≤ 50 * Real.log (2 * r * d))
    (j : ℕ) (hj : j + 2 ≤ r) (Sp : ℕ)
    (hSp : (Sp : ℝ) = ⌊2 ^ j * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)⌋₊)
    (Tp : ℕ)
    (hTp : (Tp : ℝ) = ⌊(1 - pxi r) * pxi r ^ j * pxi r ^ (r * J) * (pT r d σ : ℝ)⌋₊)
    (s : ℤ) (hss : ((|s| : ℤ) : ℝ) ≤ 2 ^ (j + 1) * pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))
    (hJP : 0.735 * pxi r ^ (j + 1 + r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * d) +
      9.30 * (2 : ℝ) ^ j * ((2 * pxi r ^ r)⁻¹) ^ J - 16.05 * (2 * pxi r) ^ j ≤ -1) :
    Real.log (7.2 * (Sp : ℝ) / (7.2 * (Sp : ℝ) - ((|s| : ℤ) : ℝ))) +
      ((d : ℝ) * (h : ℝ) * pxi r ^ (j + 1) * pxi r ^ (r * J) * (pT r d σ : ℝ) +
        1.055 * (pS r d h : ℝ) * pD r d σ +
        1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * pD r d σ +
        0.044 * (J : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ)
      - (2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1) *
          (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ)))
      < -Real.log 2 := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hξform : pxi r = 1 - 0.536/(r:ℝ) := rfl
  have hξpos : 0 < pxi r := by
    rw [hξform]
    have : 0.536/(r:ℝ) ≤ 0.268 := by rw [div_le_iff₀ hr0]; linarith
    linarith
  have hξle1 : pxi r ≤ 1 := by
    rw [hξform]
    have : 0 ≤ 0.536/(r:ℝ) := by positivity
    linarith
  set ξ : ℝ := pxi r with hξ
  set S : ℝ := (pS r d h : ℝ) with hS
  set D : ℝ := pD r d σ with hD
  set T : ℝ := (pT r d σ : ℝ) with hT
  set x : ℝ := 2 ^ j * ξ ^ (-((r * J : ℕ) : ℤ)) * S with hx
  set y : ℝ := (1 - ξ) * ξ ^ j * ξ ^ (r * J) * T with hy
  obtain ⟨hT1, hT2, hT3, hT4⟩ := num_T hr hd hh σ hσ
  have hS608 : (608:ℝ) ≤ S := by rw [hS]; exact hT4
  have hSpos : 0 < S := by linarith
  have hdhT : (d:ℝ)*(h:ℝ)*T ≤ 0.735*S*D := by rw [← hD, ← hS, ← hT] at hT3; exact hT3
  have hdT1 : 6.297 * D ≤ (1 - ξ) * T := by rw [← hD, ← hξ, ← hT] at hT1; exact hT1
  have hD1 : (1:ℝ) ≤ D := by
    have hh := (num_D_lower hr hd σ hσ).1
    rw [← hD] at hh
    have hlog : (1:ℝ) ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) := by
      have h4 : (4:ℝ) ≤ 2 * (r:ℝ) * (d:ℝ) := by nlinarith only [hr2, hd1]
      have hl4 : (1:ℝ) ≤ Real.log 4 := by
        have h4' : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
        rw [h4']; linarith [Real.log_two_gt_d9]
      exact le_trans hl4 (Real.log_le_log (by norm_num) h4)
    have hr4 : (4:ℝ) ≤ (r:ℝ)^r := by
      have h1 : (2:ℝ)^2 ≤ (r:ℝ)^2 := by nlinarith only [hr2]
      have h2 : (r:ℝ)^2 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) (by omega)
      calc (4:ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (r:ℝ)^2 := h1
        _ ≤ (r:ℝ)^r := h2
    have h32 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
      have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 32) (by omega : 3 ≤ r+1)
      calc (32768:ℝ) = 32^3 := by norm_num
        _ ≤ 32^(r+1) := h
    have hA : (1:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) := by
      have h1 : (1:ℝ) ≤ 2 * (r:ℝ)^r := by linarith
      have h12 : (1:ℝ) ≤ (2 * (r:ℝ)^r) * 32^(r+1) := by
        have := mul_le_mul h1 (by linarith : (1:ℝ) ≤ 32^(r+1)) (by norm_num) (by positivity)
        simpa using this
      have := mul_le_mul h12 hd1 (by norm_num) (by positivity)
      simpa [mul_assoc] using this
    have hmul : (1:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) := by
      have := mul_le_mul hA hlog (by norm_num) (by positivity)
      simpa using this
    linarith
  have hDpos : 0 < D := by linarith
  have hSp_le : (Sp:ℝ) ≤ x := by rw [hSp]; exact Nat.floor_le (by positivity)
  have hSp_lt : x < (Sp:ℝ) + 1 := by rw [hSp]; exact Nat.lt_floor_add_one x
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hTp_le : (Tp:ℝ) ≤ y := by rw [hTp]; exact Nat.floor_le hy0
  have hTp_lt : y < (Tp:ℝ) + 1 := by rw [hTp]; exact Nat.lt_floor_add_one y
  have hsl : ((|s| : ℤ) : ℝ) ≤ 2 * x := by
    have h2 : (2:ℝ) ^ (j+1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    calc ((|s| : ℤ) : ℝ) ≤ 2 ^ (j + 1) * ξ ^ (-((r * J : ℕ) : ℤ)) * S := by
          simpa only [hξ, hS] using hss
      _ = 2 * x := by rw [h2, hx]; ring
  have hx608 : 608 ≤ x := by
    have h2j : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hz : (1:ℝ) ≤ ξ ^ (-((r * J : ℕ) : ℤ)) := by
      have h4 : ξ ^ ((r*J : ℕ) : ℤ) ≤ 1 := by
        rw [zpow_natCast]; exact pow_le_one₀ hξpos.le hξle1
      have h5 : 0 < ξ ^ ((r*J : ℕ) : ℤ) := zpow_pos hξpos _
      rw [zpow_neg]
      exact (one_le_inv₀ h5).mpr h4
    calc (608:ℝ) = 1 * 1 * 608 := by norm_num
      _ ≤ 2 ^ j * ξ ^ (-((r * J : ℕ) : ℤ)) * S := by gcongr
  have hlogterm : Real.log (7.2 * (Sp : ℝ) / (7.2 * (Sp : ℝ) - ((|s| : ℤ) : ℝ))) ≤ 0.4 := by
    have hspos : 0 < 7.2 * (Sp:ℝ) := by linarith
    have hden : 0 < 7.2*(Sp:ℝ) - ((|s|:ℤ):ℝ) := by nlinarith only [hsl, hSp_lt, hx608]
    have hle : 7.2*(Sp:ℝ)/(7.2*(Sp:ℝ) - ((|s|:ℤ):ℝ)) ≤ 7.2/5.19 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 5.19)]
      nlinarith only [hsl, hSp_lt, hx608]
    calc Real.log (7.2 * (Sp : ℝ) / (7.2 * (Sp : ℝ) - ((|s| : ℤ) : ℝ)))
        ≤ Real.log (7.2/5.19) := Real.log_le_log (div_pos hspos hden) hle
      _ ≤ 7.2/5.19 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ ≤ 0.4 := by norm_num
  have hLAM : (1.278:ℝ) ≤ Real.log (7.2 * (Sp:ℝ)) - Real.log (max ((|s|:ℤ):ℝ) (Sp:ℝ)) := by
    have hSp607 : (607:ℝ) < (Sp:ℝ) := by linarith
    have hSp608 : (608:ℝ) ≤ (Sp:ℝ) := by
      have : (607:ℕ) < Sp := by exact_mod_cast hSp607
      exact_mod_cast (by omega : 608 ≤ Sp)
    have hMpos : 0 < max ((|s|:ℤ):ℝ) (Sp:ℝ) := by
      have : (0:ℝ) < (Sp:ℝ) := by linarith
      exact lt_of_lt_of_le this (le_max_right _ _)
    have hSp0 : (0:ℝ) < 7.2*(Sp:ℝ) := by linarith
    have hMle : max ((|s|:ℤ):ℝ) (Sp:ℝ) ≤ 2*x := by
      refine max_le hsl ?_
      linarith
    have hSpx : (607/608) * x ≤ (Sp:ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 608)]
      nlinarith only [hSp_lt, hx608, hSp_le]
    have hratio : 3.6 * (607/608) ≤ 7.2 * (Sp:ℝ) / max ((|s|:ℤ):ℝ) (Sp:ℝ) := by
      rw [le_div_iff₀ hMpos]
      nlinarith only [hMle, hSpx]
    have hpos1 : (0:ℝ) < 3.6 * (607/608) := by norm_num
    have hlog : Real.log (3.6 * (607/608)) ≤
        Real.log (7.2*(Sp:ℝ)) - Real.log (max ((|s|:ℤ):ℝ) (Sp:ℝ)) := by
      rw [← Real.log_div (ne_of_gt hSp0) (ne_of_gt hMpos)]
      exact Real.log_le_log hpos1 hratio
    have hnum : (1.278:ℝ) ≤ Real.log (3.6 * (607/608)) := by
      have h36 : Real.log 3.6 = Real.log 2 + 2 * Real.log 3 - Real.log 5 := by
        have h1 : (3.6:ℝ) = 18/5 := by norm_num
        rw [h1, Real.log_div (by norm_num : (18:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
        have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
          rw [show (18:ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
            Real.log_pow]
          norm_num
        rw [h18]
      have h607 : -(1/607:ℝ) ≤ Real.log (607/608) := by
        have h1 : Real.log (608/607) ≤ 608/607 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        have h2 : Real.log (607/608) = -Real.log (608/607) := by
          rw [show (607:ℝ)/608 = (608/607)⁻¹ by norm_num, Real.log_inv]
        rw [h2]
        have : (608:ℝ)/607 - 1 = 1/607 := by norm_num
        linarith
      have hmul : Real.log (3.6 * (607/608)) = Real.log 3.6 + Real.log (607/608) :=
        Real.log_mul (by norm_num) (by norm_num)
      rw [hmul, h36]
      linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9, h607]
    linarith
  have hpowid : ξ ^ (-((r*J:ℕ):ℤ)) * ((2:ℝ)^J)⁻¹ = ((2*ξ^r)⁻¹)^J := by
    have h1 : ((2*ξ^r)⁻¹)^J = (2*ξ^r) ^ (-(J:ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
    have h3 : (2:ℝ) ^ (-(J:ℤ)) = ((2:ℝ)^J)⁻¹ := by rw [zpow_neg, zpow_natCast]
    have key : ((ξ ^ r) ^ (-(J:ℤ))) = ξ ^ (-((r*J:ℕ):ℤ)) := by
      rw [← zpow_natCast (a := ξ) r, ← zpow_mul]
      rw [show ((r:ℤ) * (-(J:ℤ))) = -((r*J:ℕ):ℤ) by push_cast; ring]
    rw [h1, mul_zpow, h3, key]
    ring
  have hxdiv : x / 2^J = (2:ℝ)^j * ((2*ξ^r)⁻¹)^J * S := by
    rw [hx, div_eq_mul_inv, ← hpowid]
    ring
  have hscaled : 1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * D ≤
      9.2736 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J * S * D := by
    have h9 : 7.2*(Sp:ℝ) + ((|s|:ℤ):ℝ) ≤ 9.2*x := by nlinarith only [hSp_le, hsl]
    have h2J : (0:ℝ) < (2:ℝ)^J := by positivity
    have h1 : (7.2*(Sp:ℝ) + ((|s|:ℤ):ℝ))/2^J ≤ 9.2*x/2^J := div_le_div_of_nonneg_right h9 h2J.le
    have h2 : (9.2*x)/2^J = 9.2 * ((2:ℝ)^j * ((2*ξ^r)⁻¹)^J * S) := by
      rw [show (9.2*x)/2^J = 9.2*(x/2^J) by ring, hxdiv]
    calc 1.008 * ((7.2*(Sp:ℝ) + ((|s|:ℤ):ℝ))/2^J) * D
        ≤ 1.008 * (9.2*x/2^J) * D := by gcongr
      _ = 9.2736 * (2:ℝ)^j * ((2*ξ^r)⁻¹)^J * S * D := by rw [h2]; ring
  have hbracket : (d : ℝ) * (h : ℝ) * ξ ^ (j + 1) * ξ ^ (r * J) * T + 1.055 * S * D +
      1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * D +
      0.044 * (J : ℝ) / Real.log (2 * r * d) * S * D ≤ (16.05 * (2 * ξ) ^ j - 1) * S * D := by
    have hpowadd : ξ ^ (j + 1) * ξ ^ (r * J) = ξ ^ (j + 1 + r * J) := by rw [← pow_add]
    have hξj : 0 ≤ ξ ^ (j + 1) := by positivity
    have hξr : 0 ≤ ξ ^ (r * J) := by positivity
    have hpow_e : 0 ≤ (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J := by positivity
    have hSD0 : 0 ≤ S * D := mul_nonneg hSpos.le hDpos.le
    have hc3 : (d : ℝ) * (h : ℝ) * ξ ^ (j + 1) * ξ ^ (r * J) * T ≤
        0.735 * ξ ^ (j + 1) * ξ ^ (r * J) * (S * D) := by
      have hh := mul_le_mul_of_nonneg_right hdhT (mul_nonneg hξj hξr)
      nlinarith only [hh]
    have hsc : 9.2736 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J * S * D ≤
        9.30 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J * S * D := by
      nlinarith only [hpow_e, hSD0]
    have hJP2 : 0.735 * ξ ^ (j + 1) * ξ ^ (r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * d) +
          9.30 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J - 16.05 * (2 * ξ) ^ j ≤ -1 := by
      have hh := hJP
      rw [← hpowadd] at hh
      rw [← mul_assoc] at hh
      exact hh
    have hmid : (d : ℝ) * (h : ℝ) * ξ ^ (j + 1) * ξ ^ (r * J) * T + 1.055 * S * D +
        1.008 * ((7.2 * (Sp : ℝ) + ((|s| : ℤ) : ℝ)) / 2 ^ J) * D +
        0.044 * (J : ℝ) / Real.log (2 * r * d) * S * D
        ≤ (0.735 * ξ ^ (j + 1) * ξ ^ (r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * d) +
            9.30 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J) * S * D := by
      nlinarith only [hc3, hscaled, hsc]
    have hbb : (0.735 * ξ ^ (j + 1) * ξ ^ (r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * d) +
            9.30 * (2 : ℝ) ^ j * ((2 * ξ ^ r)⁻¹) ^ J) * S * D ≤ (16.05 * (2 * ξ) ^ j - 1) * S * D := by
      nlinarith only [hJP2, hSD0]
    linarith [hmid, hbb]
  have hq_le : 6.297 * (ξ ^ j * ξ ^ (r * J)) * D ≤ y := by
    have hfac : 0 ≤ ξ ^ j * ξ ^ (r * J) := by positivity
    have hh := mul_le_mul_of_nonneg_right hdT1 hfac
    rw [hy]
    nlinarith only [hh]
  have hNeg : 16.06 * (2 * ξ) ^ j * S * D ≤
      (2 * (Sp : ℝ) + 1) * ((Tp : ℝ) + 1) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ))) := by
    have hcancel : ξ ^ (-((r*J:ℕ):ℤ)) * ξ ^ (r*J) = 1 := by
      rw [← zpow_natCast (a := ξ) (r*J), ← zpow_add₀ (ne_of_gt hξpos), neg_add_cancel, zpow_zero]
    have hxj : 0 < ξ^j := pow_pos hξpos j
    have hrJ : 0 < ξ^(r*J) := pow_pos hξpos _
    have hA : 2*x*(1215/1216) ≤ 2*x - 1 := by nlinarith only [hx608]
    have h2x1 : 0 ≤ 2*x - 1 := by linarith
    have hq0 : 0 ≤ 6.297*(ξ^j*ξ^(r*J))*D := by positivity
    have hTpq : 6.297*(ξ^j*ξ^(r*J))*D ≤ (Tp:ℝ)+1 := le_trans hq_le hTp_lt.le
    have hΛ0 : 0 ≤ Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ)) := by
      linarith
    have h2Sp : 2*x - 1 ≤ 2*(Sp:ℝ) + 1 := by linarith [hSp_lt]
    have hstep1 : 2*x*(1215/1216) * (6.297*(ξ^j*ξ^(r*J))*D) * 1.278 ≤ (2*x - 1) * (6.297*(ξ^j*ξ^(r*J))*D) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ))) := by
      have h1 : 2*x*(1215/1216) * (6.297*(ξ^j*ξ^(r*J))*D) ≤ (2*x - 1) * (6.297*(ξ^j*ξ^(r*J))*D) :=
        mul_le_mul hA le_rfl hq0 h2x1
      exact mul_le_mul h1 hLAM (by norm_num) (mul_nonneg h2x1 hq0)
    have hstep2 : (2*x - 1) * (6.297*(ξ^j*ξ^(r*J))*D) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ))) ≤
        (2*(Sp:ℝ)+1) * ((Tp:ℝ)+1) *
        (Real.log (7.2 * (Sp : ℝ)) - Real.log (max ((|s| : ℤ) : ℝ) (Sp : ℝ))) := by
      have h1 : (2*x-1)*(6.297*(ξ^j*ξ^(r*J))*D) ≤ (2*(Sp:ℝ)+1)*((Tp:ℝ)+1) :=
        mul_le_mul h2Sp hTpq hq0 (by positivity)
      exact mul_le_mul h1 le_rfl hΛ0 (by positivity)
    have hstep3 : 16.06 * (2*ξ)^j * S * D ≤ 2*x*(1215/1216) * (6.297*(ξ^j*ξ^(r*J))*D) * 1.278 := by
      rw [mul_pow]
      rw [hx]
      have hid : 2 * (2 ^ j * ξ ^ (-((r*J:ℕ):ℤ)) * S) * (1215 / 1216) *
            (6.297 * (ξ ^ j * ξ ^ (r * J)) * D) * 1.278
          = (2*(1215/1216)*6.297*1.278) * ((2:ℝ)^j * ξ^j * S * D) *
              (ξ ^ (-((r*J:ℕ):ℤ)) * ξ ^ (r * J)) := by ring
      rw [hid, hcancel, mul_one]
      have hcoef : (16.06:ℝ) ≤ 2*(1215/1216)*6.297*1.278 := by norm_num
      have hX : 0 ≤ (2:ℝ)^j * ξ^j * S * D := by positivity
      nlinarith only [hcoef, hX]
    linarith [hstep1, hstep2, hstep3]
  have hpow2 : 0 ≤ (2 * ξ) ^ j := by positivity
  have hSD : (2:ℝ) ≤ S * D := by nlinarith only [hS608, hD1]
  nlinarith only [hlogterm, hbracket, hNeg, hpow2, hSD, Real.log_two_lt_d9]

end Work.BW
