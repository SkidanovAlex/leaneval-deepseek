/-
# `Submission.Work.FIArea7CF.Area7AssemblyB` — the assembly of the amended round-6 area 7

See the header of `Submission/Work/FIArea7/area7_6b.lean` and `AREA7_ROUTE_LEAD.md` §2.2 (A8).
-/
import Mathlib
import Submission.Work.FIArea7CF.Area7BDefs
import Submission.Work.FIArea7CF.Area7Assembly6
import Submission.Work.FIArea7CF.regionHighSlack_le
import Submission.Work.FIArea7CF.guard_clashfree_le
import Submission.Work.FIArea7CF.strip_bound6
import Submission.Work.FIArea7CF.pairW_pair_sum_le
import Submission.Work.FIArea7CF.numeric_core_proof_B
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.isBetaCoeff6_split
import Submission.Work.FIArea7.deltaTau_mass_le
import Submission.Work.FIArea7CF.deltaQ_mass_le
import Submission.Work.FIArea7.uniSChar_betaL_le
import Submission.Work.FIArea7.charRegionLowSlackUse_le
import Submission.Work.FIArea7.charRegionLow_pair_sharp_le
import Submission.Work.FIArea7CF.charRegionLow_split_le
import Submission.Work.FIArea7.reflSign_eq_one_of_axisFree
import Submission.Work.FIArea7.nine_theta_le_vartheta
import Submission.Work.FIArea7.modeLen_bounds
import Submission.Work.FIArea7.modeLen_log_le
import Submission.Work.FIArea7.area7_small_theta
import Submission.Work.FIArea7.isBetaCoeff6_mass_caps
import Submission.Work.FIArea7.EngineSharp6
import Submission.Work.FIArea7.NCBasic

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Three inputs that are pure instantiations -/

theorem capsBoundB : CapsBound := fun hβ => isBetaCoeff6_mass_caps hβ

theorem engineBoundB : EngineBound :=
  WUniOmega6Pull6_sub_Moll_le_sharp_aux pairW_pair_sum_le

theorem guardBoundB : GuardBound := guard_clashfree_le

/-! ## 2. The assembly -/

theorem Area7Uni6B_of_pieces (h172 : Prop172Classical) : Area7Uni6B := by
  classical
  obtain ⟨C_L, hCL, hLowT⟩ := charRegionLowSlackUse_le
  obtain ⟨C_P, hCP, hPair⟩ := charRegionLow_pair_sharp_le
  obtain ⟨C_X, hCX, hSplit⟩ := charRegionLow_split_le
  obtain ⟨C_H, Clat, hCH, hClat, hHigh⟩ := regionHighSlack_le
  obtain ⟨C_Q, hCQ, hQ⟩ := deltaQ_mass_le
  obtain ⟨x3, hTau⟩ := deltaTau_mass_le
  obtain ⟨xm, hMode⟩ := modeLen_bounds
  obtain ⟨xML, hModeLog⟩ := modeLen_log_le
  obtain ⟨Cs, hCs, hSmallTheta⟩ := area7_small_theta
  obtain ⟨Cst, xst, hCst, hStrip⟩ := strip_bound6
  obtain ⟨C_E, hCE, hEng⟩ := engineBoundB
  obtain ⟨C_G, hCG, hGuard⟩ := guardBoundB
  have hCaps : CapsBound := capsBoundB
  intro η hη0 hηlt
  obtain ⟨δ5, c5, x5, hδ5, hc5, hA5⟩ := uniSChar_betaL_le h172 η hη0 hηlt
  set δ₁ : ℝ := min δ5 (3 / 64) with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min hδ5 (by norm_num)
  have hδ₁lt : δ₁ < 3 / 32 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ₁le5 : δ₁ ≤ δ5 := min_le_left _ _
  obtain ⟨cN, N₀, hcN, hNum⟩ := Work.FIArea7CF.numeric_core_proof_B C_L C_H C_E C_G c5 Clat C_P C_X C_Q
    (5 * 10 ^ 9) hCL hCH hCE hCG hc5 hClat hCP hCX hCQ (by norm_num) δ₁ hδ₁pos hδ₁lt
  refine ⟨δ₁ / 8, max (2 * Cs + Cst) cN,
    |x5| + |x3| + |xm| + |xML| + |xst| + (10 : ℝ) ^ 16 + (max N₀ 1) ^ 4 + 1,
    by positivity, lt_of_lt_of_le hcN (le_max_right _ _), ?_⟩
  intro Pa hx hηPa hτ X φ z0 β hβ hfar hX hXδ hXcap
  -- ### the thresholds
  set X0 : ℝ := |x5| + |x3| + |xm| + |xML| + |xst| + (10 : ℝ) ^ 16 + (max N₀ 1) ^ 4 + 1
    with hX0
  have hN04 : (0 : ℝ) ≤ (max N₀ 1) ^ 4 :=
    pow_nonneg (le_trans zero_le_one (le_max_right N₀ 1)) 4
  have hx5 : x5 ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, le_abs_self x5, abs_nonneg x3, abs_nonneg xm, abs_nonneg xML,
      abs_nonneg xst, hN04]
  have hx3' : x3 ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, le_abs_self x3, abs_nonneg x5, abs_nonneg xm, abs_nonneg xML,
      abs_nonneg xst, hN04]
  have hxm' : xm ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, le_abs_self xm, abs_nonneg x5, abs_nonneg x3, abs_nonneg xML,
      abs_nonneg xst, hN04]
  have hxML' : xML ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, le_abs_self xML, abs_nonneg x5, abs_nonneg x3, abs_nonneg xm,
      abs_nonneg xst, hN04]
  have hxst' : xst ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, le_abs_self xst, abs_nonneg x5, abs_nonneg x3, abs_nonneg xm,
      abs_nonneg xML, hN04]
  have hx16 : (10 : ℝ) ^ 16 ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, abs_nonneg x5, abs_nonneg x3, abs_nonneg xm, abs_nonneg xML,
      abs_nonneg xst, hN04]
  have hxN0 : (max N₀ 1) ^ 4 ≤ (Pa.x : ℝ) := by
    rw [hX0] at hx
    linarith only [hx, abs_nonneg x5, abs_nonneg x3, abs_nonneg xm, abs_nonneg xML,
      abs_nonneg xst, hN04]
  -- ### `N` is large
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := le_trans (by norm_num) hx16
  have hx4 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [Pa.hη])
  have hxq : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) < Pa.N := lt_of_le_of_lt hx4 Pa.hNlo
  have hN₀_le : N₀ ≤ Pa.N := by
    have hM0 : (0 : ℝ) ≤ max N₀ 1 := le_trans zero_le_one (le_max_right _ _)
    have h1 : ((max N₀ 1) ^ 4) ^ ((1 : ℝ) / 4) = max N₀ 1 := by
      rw [← Real.rpow_natCast (max N₀ 1) 4, ← Real.rpow_mul hM0]
      norm_num
    calc N₀ ≤ max N₀ 1 := le_max_left _ _
      _ = ((max N₀ 1) ^ 4) ^ ((1 : ℝ) / 4) := h1.symm
      _ ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hxN0 (by norm_num)
      _ ≤ Pa.N := le_of_lt hxq
  have hN3 : (3 : ℝ) ≤ Pa.N := by
    have h1 : ((10 : ℝ) ^ 16) ^ ((1 : ℝ) / 4) = (10 : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast (10 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    have h2 : (10 : ℝ) ^ 4 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hx16 (by norm_num)
    linarith only [h2, hx4, Pa.hNlo]
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith only [hN3]
  have hNpos : (0 : ℝ) < Pa.N := by linarith only [hN1]
  have hlog3ge : (1 : ℝ) ≤ Real.log 3 := by
    have h : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith only [Real.exp_one_lt_three]
    exact le_of_lt h
  have hlogN1 : (1 : ℝ) ≤ Real.log Pa.N :=
    le_trans hlog3ge (Real.log_le_log (by norm_num) (by linarith only [hN3]))
  have hNlog1 : (1 : ℝ) ≤ Real.log (Pa.N + 2) :=
    le_trans hlogN1 (Real.log_le_log (by linarith only [hN1]) (by linarith only [hN1]))
  have hLnn : (0 : ℝ) ≤ Real.log Pa.N := le_trans zero_le_one hlogN1
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hPz0 : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have h : (0 : ℕ) < Pa.Pz := lt_of_lt_of_le Nat.zero_lt_two Pa.hP2
    exact_mod_cast h
  have hPz1 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ := inv_nonneg.mpr hPz0.le
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXinv0 : (0 : ℝ) ≤ ((X : ℝ))⁻¹ := inv_nonneg.mpr (by linarith only [hX1])
  have hX8 : (X : ℝ) ^ 8 ≤ Pa.N ^ δ₁ := by
    have h1 : (X : ℝ) ^ 8 ≤ ((Pa.N : ℝ) ^ (δ₁ / 8)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (le_of_lt hXδ) 8
    have h2 : ((Pa.N : ℝ) ^ (δ₁ / 8)) ^ 8 = Pa.N ^ δ₁ := by
      rw [← Real.rpow_natCast ((Pa.N : ℝ) ^ (δ₁ / 8)) 8,
        ← Real.rpow_mul (by linarith only [hN1] : (0 : ℝ) ≤ (Pa.N : ℝ))]
      congr 1
      ring
    linarith only [h1, h2]
  have hX9 : (X : ℝ) ^ 9 ≤ Pa.N := by
    have h1 : (X : ℝ) ^ 9 = (X : ℝ) ^ 8 * (X : ℝ) := by ring
    have h3 : (X : ℝ) ≤ Pa.N ^ (δ₁ / 8) := le_of_lt hXδ
    have h4 : (X : ℝ) ^ 8 * (X : ℝ) ≤ Pa.N ^ δ₁ * Pa.N ^ (δ₁ / 8) :=
      mul_le_mul hX8 h3 (by positivity) (by positivity)
    have h5 : Pa.N ^ δ₁ * Pa.N ^ (δ₁ / 8) = Pa.N ^ (δ₁ + δ₁ / 8) := by
      rw [← Real.rpow_add (by linarith only [hN1] : (0 : ℝ) < Pa.N)]
    have h6 : Pa.N ^ (δ₁ + δ₁ / 8) ≤ Pa.N := by
      have h := Real.rpow_le_rpow_of_exponent_le hN1
        (show δ₁ + δ₁ / 8 ≤ 1 by linarith only [hδ₁lt])
      rwa [Real.rpow_one] at h
    rw [h1]
    linarith only [h4, h5, h6]
  -- ### the parameter `K`, the mode length `Lm` and the slack `L₀`
  set K : ℕ := ⌈(X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20⌉₊ with hKdef
  set Lm : ℕ := modeLen Pa X with hLmdef
  set L₀ : ℕ := 2 * K + 2 * Lm + 2 with hL₀def
  have hKpos : (0 : ℝ) < (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 := by
    have h1 : (0 : ℝ) < (X : ℝ) := by linarith only [hX1]
    have h2 : (0 : ℝ) < Real.log (Pa.N + 2) := by linarith only [hNlog1]
    exact mul_pos (pow_pos h1 3) (pow_pos h2 20)
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    exact Nat.one_le_ceil_iff.mpr hKpos
  have hKg : (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 ≤ (K : ℝ) := by
    rw [hKdef]; exact Nat.le_ceil _
  have hKu : (K : ℝ) ≤ 2 * (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 := by
    have h1 : (K : ℝ) ≤ (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 + 1 := by
      rw [hKdef]
      exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt hKpos))
    have h2 : (1 : ℝ) ≤ (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 := by
      have h3 : (1 : ℝ) ≤ (X : ℝ) ^ 3 := by
        calc (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
          _ ≤ (X : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hX1 3
      have h4 : (1 : ℝ) ≤ (Real.log (Pa.N + 2)) ^ 20 := by
        calc (1 : ℝ) = (1 : ℝ) ^ 20 := by norm_num
          _ ≤ (Real.log (Pa.N + 2)) ^ 20 := pow_le_pow_left₀ (by norm_num) hNlog1 20
      nlinarith only [h3, h4]
    linarith only [h1, h2]
  have hLm1 : 1 ≤ Lm := by
    rw [hLmdef, modeLen]
    have h1 : 1 ≤ Nat.ceil Pa.θ⁻¹ := Nat.one_le_ceil_iff.mpr (inv_pos.mpr hθ0)
    have h3 : 1 ≤ Nat.ceil (Real.log (Pa.N + 2)) ^ 6 := by
      have hc : 1 ≤ Nat.ceil (Real.log (Pa.N + 2)) := Nat.one_le_ceil_iff.mpr (by linarith only [hNlog1])
      calc (1 : ℕ) = 1 ^ 6 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left hc 6
    calc (1 : ℕ) = 1 * 1 * 1 := by norm_num
      _ ≤ Nat.ceil Pa.θ⁻¹ * X * Nat.ceil (Real.log (Pa.N + 2)) ^ 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 hX) h3
  have hLm1r : (1 : ℝ) ≤ (Lm : ℝ) := by exact_mod_cast hLm1
  have hLmp : (0 : ℝ) < (Lm : ℝ) := by linarith only [hLm1r]
  have hL₀le : (L₀ : ℝ) ≤ 2 * (K : ℝ) + 2 * (Lm : ℝ) + 2 := by
    rw [hL₀def]; push_cast; ring_nf
    norm_num
  have hUB : (0 : ℝ) < (uniB Pa : ℝ) := by
    unfold Work.FIArea7.uniB
    push_cast
    positivity
  have hUB4 : (uniB Pa : ℝ) ≤ 4 * Pa.θ * Pa.N + 2 := by
    unfold Work.FIArea7.uniB
    have hq0 : (0 : ℝ) ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 := by positivity
    have h5 : ((⌈2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4⌉₊ : ℕ) : ℝ)
        ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 + 1 :=
      le_of_lt (Nat.ceil_lt_add_one hq0)
    have hpi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
    have h4 : (1 + Pa.θ) ≤ 2 := by linarith only [hθ1]
    have h1 : 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 ≤ 4 * Pa.θ * Pa.N := by
      have hA : 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4
          = (Real.pi * (1 + Pa.θ) / 2) * (Pa.θ * Pa.N) := by ring
      rw [hA]
      have hθ0' : (0 : ℝ) ≤ 1 + Pa.θ := by linarith only [hθ0.le]
      have hB : Real.pi * (1 + Pa.θ) / 2 ≤ 4 := by nlinarith only [hpi, h4, hθ0']
      have hC : (0 : ℝ) ≤ Pa.θ * Pa.N := mul_nonneg hθ0.le (by linarith only [hN1])
      nlinarith only [mul_le_mul_of_nonneg_right hB hC]
    push_cast
    linarith only [h5, h1]
  have hcaps := hCaps hβ
  have hE2nn : (0 : ℝ) ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 := by
    positivity
  have hE2' : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 3 := by
    have h := hcaps.2
    rw [CapsE2] at h
    simpa only [add_comm] using h
  have h9 : 9 * Pa.θ ≤ Pa.ϑ := nine_theta_le_vartheta Pa
  have hε1 : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2
        = (fun _ => 1 : GaussianInt → ℤ) z1 * (fun _ => 1 : GaussianInt → ℤ) z2 := by
    intro z1 z2 h1 h2
    rw [reflSign_eq_one_of_axisFree hfar h9 z1 z2 h1 h2]
    norm_num
  by_cases hsmall : Pa.θ ^ 2 * Pa.τ * (X : ℝ) ≤ 1
  · -- ### the trivial regime `θ²τX ≤ 1`
    have hτX2 : Pa.τ * (X : ℝ) ^ 2 ≤ Pa.N := by
      have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by
        exact_mod_cast (by linarith [Pa.hx] : (0 : ℕ) < Pa.x)
      have hexp : (0 : ℝ) < (1 : ℝ) / 4 + Pa.η := by linarith only [Pa.hη]
      have hX2 : (X : ℝ) ^ 2 ≤ Pa.N ^ (δ₁ / 4) := by
        have h1 : ((X : ℝ) ^ 2) ^ 4 ≤ Pa.N ^ δ₁ := by
          rw [← pow_mul]; norm_num; exact hX8
        calc (X : ℝ) ^ 2 = (((X : ℝ) ^ 2) ^ 4) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast ((X : ℝ) ^ 2) 4, ← Real.rpow_mul (sq_nonneg _)]
              norm_num
          _ ≤ (Pa.N ^ δ₁) ^ ((1 : ℝ) / 4) :=
              Real.rpow_le_rpow (by positivity) h1 (by norm_num)
          _ = Pa.N ^ (δ₁ / 4) := by
              rw [← Real.rpow_mul hNpos.le]; congr 1; ring
      have hxη : (Pa.x : ℝ) ^ (Pa.η / 3) ≤ Pa.N ^ ((1 : ℝ) / 8) := by
        have hq : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ (Pa.η / 3 / ((1 : ℝ) / 4 + Pa.η))
            = (Pa.x : ℝ) ^ (Pa.η / 3) := by
          have h4 : (1 : ℝ) + 4 * Pa.η ≠ 0 := by
            intro hcon
            nlinarith only [hcon, Pa.hη]
          rw [← Real.rpow_mul hxpos.le]
          congr 1
          field_simp
        rw [← hq]
        calc ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ (Pa.η / 3 / ((1 : ℝ) / 4 + Pa.η))
            ≤ Pa.N ^ (Pa.η / 3 / ((1 : ℝ) / 4 + Pa.η)) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) (le_of_lt Pa.hNlo)
                (div_nonneg (div_nonneg Pa.hη.le (by norm_num)) hexp.le)
          _ ≤ Pa.N ^ ((1 : ℝ) / 8) :=
              Real.rpow_le_rpow_of_exponent_le hN1
                (by rw [div_le_iff₀ hexp]; nlinarith only [Pa.hη, hηPa, hηlt, hexp])
      have hA : Pa.τ * (X : ℝ) ^ 2 ≤ Pa.N ^ ((1 : ℝ) / 8) * Pa.N ^ (δ₁ / 4) :=
        mul_le_mul (le_trans Pa.hτ2 hxη) hX2 (by positivity) (Real.rpow_nonneg hNpos.le _)
      have hB : Pa.N ^ ((1 : ℝ) / 8) * Pa.N ^ (δ₁ / 4) = Pa.N ^ ((1 : ℝ) / 8 + δ₁ / 4) := by
        rw [← Real.rpow_add hNpos]
      have hC : Pa.N ^ ((1 : ℝ) / 8 + δ₁ / 4) ≤ Pa.N := by
        have h := Real.rpow_le_rpow_of_exponent_le hN1
          (show (1 : ℝ) / 8 + δ₁ / 4 ≤ 1 by linarith only [hδ₁lt])
        rwa [Real.rpow_one] at h
      linarith only [hA, hB, hC]
    have hsm := hSmallTheta (Pa := Pa) (X := X) (φ := φ) (z0 := z0) (β := β)
      hβ hX hsmall hτX2
    have hst := hStrip Pa hxst' X φ z0 β hβ hX hX9
    have hWu := WUni6_eq_Wcut6_add_Bcut6_add_Strip6 Pa X β
    have hlog2 : Real.log (Pa.N + 2) ≤ 2 * Real.log Pa.N :=
      log_add_two_le_two_mul_log (by linarith only [hN3])
    have hnn : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
      mul_nonneg (mul_nonneg (add_nonneg hPz1 hXinv0) (by positivity)) hLnn
    have hCspos : (0 : ℝ) ≤ Cs := hCs.le
    have hstep1 : ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
        ≤ 2 * (((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := by
      have hXl : (0 : ℝ) ≤ ((X : ℝ))⁻¹ * Pa.N ^ 2 :=
        mul_nonneg hXinv0 (sq_nonneg _)
      calc ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
          = (((X : ℝ))⁻¹ * Pa.N ^ 2) * Real.log (Pa.N + 2) := by ring
        _ ≤ (((X : ℝ))⁻¹ * Pa.N ^ 2) * (2 * Real.log Pa.N) :=
            mul_le_mul_of_nonneg_left hlog2 hXl
        _ = 2 * (((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := by ring
    have hstep2 : ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
      have hNl : (0 : ℝ) ≤ Pa.N ^ 2 * Real.log Pa.N := mul_nonneg (sq_nonneg _) hLnn
      calc ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log Pa.N
          = ((X : ℝ))⁻¹ * (Pa.N ^ 2 * Real.log Pa.N) := by ring
        _ ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * (Pa.N ^ 2 * Real.log Pa.N) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hPz1) hNl
        _ = ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by ring
    have hstep3 : ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
        ≤ 2 * (((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N) := by
      calc ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
          ≤ 2 * (((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := hstep1
        _ ≤ 2 * (((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N) := by
            linarith only [hstep2]
    have hkey1 : Cs * ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
        ≤ (2 * Cs) * (((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N) := by
      calc Cs * ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
          = Cs * (((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)) := by ring
        _ ≤ Cs * (2 * (((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N)) :=
            mul_le_mul_of_nonneg_left hstep3 hCspos
        _ = (2 * Cs) * (((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N) := by ring
    calc ‖WUni6 Pa X β‖
        = ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
            + Work.FITop4.Bcut (Work.FITop.radN Pa) X β) + Strip6 Pa X β‖ := by rw [hWu]
      _ ≤ ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β
            + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖ + ‖Strip6 Pa X β‖ := norm_add_le _ _
      _ ≤ Cs * ((X : ℝ))⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
            + Cst * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
          add_le_add hsm hst
      _ ≤ (2 * Cs + Cst) * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
          calc Cs * (↑X)⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2)
                + Cst * ((↑Pa.Pz)⁻¹ + (↑X)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
              ≤ 2 * Cs * (((↑Pa.Pz)⁻¹ + (↑X)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)
                + Cst * ((↑Pa.Pz)⁻¹ + (↑X)⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
                add_le_add hkey1 le_rfl
            _ = (2 * Cs + Cst) * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
                ring
      _ ≤ max (2 * Cs + Cst) cN * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
          have hle : (2 * Cs + Cst) ≤ max (2 * Cs + Cst) cN := le_max_left _ _
          have hA0 : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := hnn
          nlinarith only [hle, hA0]
  -- ### the main regime `θ²τX > 1`
  push Not at hsmall
  have hLmge : Pa.θ⁻¹ * (X : ℝ) * (Real.log (Pa.N + 2)) ^ 6 ≤ (Lm : ℝ) := by
    rw [hLmdef]; exact (hMode Pa X hxm' hX hXcap).1
  have hLmLog : (Lm : ℝ) ≤ (Real.log Pa.N) ^ (5 * 10 ^ 9 : ℝ) := by
    rw [hLmdef]
    exact hModeLog Pa X hxML' hX hXcap hτ hsmall
  rcases isBetaCoeff6_split hβ hfar h9 with hzero | ⟨q, p, hqpi, hφlo, hφhi, hβeq⟩
  · -- ### `β ≡ 0`
    have hz : WUni6 Pa X β = 0 := by
      simp [WUni6, Work.FITop4.Tcut, hzero]
    rw [hz, norm_zero]
    have hcpos : (0 : ℝ) < max (2 * Cs + Cst) cN := lt_of_lt_of_le hcN (le_max_right _ _)
    exact mul_nonneg (mul_nonneg (mul_nonneg hcpos.le (add_nonneg hPz1 hXinv0))
      (sq_nonneg _)) hLnn
  -- ### the `L²`-mass of `E := β − β_L`
  set E : GaussianInt → ℂ := fun z => β z - betaL Pa q p φ z0 Lm z with hEdef
  have hEvnn : (0 : ℝ) ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2 := by positivity
  have hEv : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2)
      ≤ 2 * Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ))
        + 2 * C_Q * Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
            / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5) := by
    have hδτ := hTau Pa q p φ z0 hx3' hτ hqpi
    have hβL0 := hQ q p φ z0 Lm hqpi hφlo hφhi hLm1
    have hβL : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2)
        ≤ C_Q * ((Pa.θ⁻¹ * Real.log ((Lm : ℝ) + 2) / (Lm : ℝ)) ^ 2
            * (Pa.N * (Real.log (Pa.N + 2)) ^ 7)) := by
      have h := hβL0
      linarith only [h]
    have hXlog6 : (0 : ℝ) < (X : ℝ) * (Real.log (Pa.N + 2)) ^ 6 := by
      have : (0 : ℝ) < Real.log (Pa.N + 2) := by linarith only [hNlog1]
      positivity
    have hratio : Pa.θ⁻¹ / (Lm : ℝ) ≤ 1 / ((X : ℝ) * (Real.log (Pa.N + 2)) ^ 6) := by
      rw [div_le_div_iff₀ hLmp hXlog6]
      linarith only [hLmge, hLmp, hXlog6]
    have hratio2 : (Pa.θ⁻¹ / (Lm : ℝ)) ^ 2
        ≤ (1 / ((X : ℝ) * (Real.log (Pa.N + 2)) ^ 6)) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (inv_nonneg.mpr hθ0.le) hLmp.le) hratio 2
    have hkey : (Pa.θ⁻¹ * Real.log ((Lm : ℝ) + 2) / (Lm : ℝ)) ^ 2
          * (Pa.N * (Real.log (Pa.N + 2)) ^ 7)
        ≤ Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
            / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5) := by
      have hXne : (X : ℝ) ≠ 0 := by positivity
      have hlne : Real.log (Pa.N + 2) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hNlog1)
      have hLnne : Real.log ((Lm : ℝ) + 2) ≠ 0 := by
        have h3 : (1 : ℝ) ≤ Real.log ((Lm : ℝ) + 2) :=
          le_trans hlog3ge (Real.log_le_log (by norm_num) (by linarith only [hLm1r]))
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one h3)
      have h4 : (Pa.θ⁻¹ * Real.log ((Lm : ℝ) + 2) / (Lm : ℝ)) ^ 2
          = (Pa.θ⁻¹ / (Lm : ℝ)) ^ 2 * (Real.log ((Lm : ℝ) + 2)) ^ 2 := by
        rw [mul_div_assoc, div_pow]; ring
      have h6 : (1 / ((X : ℝ) * (Real.log (Pa.N + 2)) ^ 6)) ^ 2
            * (Real.log ((Lm : ℝ) + 2)) ^ 2 * (Real.log (Pa.N + 2)) ^ 7
          = (Real.log ((Lm : ℝ) + 2)) ^ 2
              / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5) := by
        field_simp
      rw [h4]
      calc (Pa.θ⁻¹ / (Lm : ℝ)) ^ 2 * (Real.log ((Lm : ℝ) + 2)) ^ 2
            * (Pa.N * (Real.log (Pa.N + 2)) ^ 7)
          ≤ ((1 / ((X : ℝ) * (Real.log (Pa.N + 2)) ^ 6)) ^ 2
              * (Real.log ((Lm : ℝ) + 2)) ^ 2) * (Pa.N * (Real.log (Pa.N + 2)) ^ 7) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hratio2 (sq_nonneg _)) (by positivity)
        _ = Pa.N * ((1 / ((X : ℝ) * (Real.log (Pa.N + 2)) ^ 6)) ^ 2
              * (Real.log ((Lm : ℝ) + 2)) ^ 2 * (Real.log (Pa.N + 2)) ^ 7) := by ring
        _ = Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
              / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5) := by
            rw [h6]; ring
    have hkey2 : C_Q * ((Pa.θ⁻¹ * Real.log ((Lm : ℝ) + 2) / (Lm : ℝ)) ^ 2
          * (Pa.N * (Real.log (Pa.N + 2)) ^ 7))
        ≤ C_Q * (Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
            / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5)) :=
      mul_le_mul_of_nonneg_left hkey hCQ.le
    -- the pointwise split of `E`
    have hBpt : ∀ z, ‖E z‖ ^ 2
        ≤ 2 * ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2
          + 2 * ‖betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2 := by
      intro z
      have hrew : E z = (betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z)
          - betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1) := by
        simp only [hEdef]
        rw [hβeq z]
        by_cases hc : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ <;>
          simp [hc] <;> ring
      rw [hrew]
      have h1 : ‖(betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z)
            - betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖
          ≤ ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖
            + ‖betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ :=
        norm_sub_le _ _
      have h2 : ‖(betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z)
            - betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2
          ≤ (‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖
            + ‖betaTilde Pa q p φ z0 z
              * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith only [h2, sq_nonneg (‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖
          - ‖betaTilde Pa q p φ z0 z
            * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖)]
    have hsum : ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2
        ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (2 * ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2
              + 2 * ‖betaTilde Pa q p φ z0 z
                  * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2) :=
      Finset.sum_le_sum (fun z _ => hBpt z)
    have hsum2 : ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (2 * ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2
              + 2 * ‖betaTilde Pa q p φ z0 z
                  * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2)
        = 2 * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2)
          + 2 * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖betaTilde Pa q p φ z0 z
                * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2
        ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (2 * ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2
              + 2 * ‖betaTilde Pa q p φ z0 z
                  * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2) := hsum
      _ = 2 * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖betaTilde Pa q p φ z0 z - betaL Pa q p φ z0 Lm z‖ ^ 2)
          + 2 * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖betaTilde Pa q p φ z0 z
                * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ ^ 2) := hsum2
      _ ≤ 2 * (C_Q * ((Pa.θ⁻¹ * Real.log ((Lm : ℝ) + 2) / (Lm : ℝ)) ^ 2
              * (Pa.N * (Real.log (Pa.N + 2)) ^ 7)))
          + 2 * (Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ))) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hβL (by norm_num))
              (mul_le_mul_of_nonneg_left hδτ (by norm_num))
      _ ≤ 2 * (C_Q * (Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
              / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5)))
          + 2 * (Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ))) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hkey2 (by norm_num)) le_rfl
      _ = 2 * Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ))
          + 2 * C_Q * Pa.N * (Real.log ((Lm : ℝ) + 2)) ^ 2
              / ((X : ℝ) ^ 2 * (Real.log (Pa.N + 2)) ^ 5) := by ring
  -- ### the region-I pieces at `u = β_L`, `E = β − β_L`
  have hLmnn : (0 : ℝ) ≤ (Lm : ℝ) := by positivity
  have hδN : Pa.N ^ δ₁ ≤ Pa.N ^ δ5 := Real.rpow_le_rpow_of_exponent_le hN1 hδ₁le5
  have hhypA : ∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (GaussUnit Q)) ℂ),
      (Q : ℝ) * (|(k : ℝ)| + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁ → |(k : ℝ)| ≤ 2 * (K : ℝ) →
      ‖uniSChar Pa Q (fun _ => 1) (fun z => betaL Pa q p φ z0 Lm z) k χ‖
        ≤ c5 * Pa.N ^ (1 - δ₁) := by
    intro Q _ k χ hQ hk
    have hkey : 2 * (|(k : ℝ)| + (Lm : ℝ) + 1) ≤ |(k : ℝ)| + (L₀ : ℝ) + 2 := by
      rw [hL₀def]; push_cast; nlinarith only [hk, hLmnn, abs_nonneg ((k : ℝ))]
    have h5 : 2 * (Q : ℝ) * (|(k : ℝ)| + (Lm : ℝ) + 1)
        = (Q : ℝ) * (2 * (|(k : ℝ)| + (Lm : ℝ) + 1)) := by ring
    have h2 : 2 * (Q : ℝ) * (|(k : ℝ)| + (Lm : ℝ) + 1) ≤ Pa.N ^ δ5 := by
      rw [h5]
      linarith only [mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg Q), hδN, hQ]
    have h6 := hA5 Pa hx5 hηPa q p φ z0 Lm hqpi hφlo hφhi hLm1 Q k χ h2
    exact le_trans h6 (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ₁le5])) hc5.le)
  have hhypB : ∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (GaussUnit Q)) ℂ),
      (Q : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁ → |(k : ℝ)| ≤ 2 * (K : ℝ) →
      ‖uniSChar Pa Q (fun _ => 1) (fun z => betaL Pa q p φ z0 Lm z) k χ‖
        ≤ c5 * Pa.N ^ (1 - δ₁) := by
    intro Q _ k χ hQ hk
    have hkey : 2 * (|(k : ℝ)| + (Lm : ℝ) + 1) ≤ 2 * (K : ℝ) + (L₀ : ℝ) + 2 := by
      rw [hL₀def]; push_cast; nlinarith only [hk, hLmnn, abs_nonneg ((k : ℝ))]
    have h5 : 2 * (Q : ℝ) * (|(k : ℝ)| + (Lm : ℝ) + 1)
        = (Q : ℝ) * (2 * (|(k : ℝ)| + (Lm : ℝ) + 1)) := by ring
    have h2 : 2 * (Q : ℝ) * (|(k : ℝ)| + (Lm : ℝ) + 1) ≤ Pa.N ^ δ5 := by
      rw [h5]
      linarith only [mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg Q), hδN, hQ]
    have h6 := hA5 Pa hx5 hηPa q p φ z0 Lm hqpi hφlo hφhi hLm1 Q k χ h2
    exact le_trans h6 (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ₁le5])) hc5.le)
  have hsnn : (0 : ℝ) ≤ c5 * Pa.N ^ (1 - δ₁) :=
    mul_nonneg hc5.le (Real.rpow_nonneg hNpos.le _)
  have hT1 := hLowT (Pa := Pa) (X := X) (K := K) (L₀ := L₀)
    (u := fun z => betaL Pa q p φ z0 Lm z) (δ₁ := δ₁) (c₁ := c5) hK1 hδ₁pos hc5 hhypA
  have hT5 := hPair (Pa := Pa) (X := X) (K := K) (L₀ := L₀) (δ₁ := δ₁) E (fun _ => 1)
    hX hK1 hδ₁pos (fun z => by norm_num)
  have hT6 := hSplit (Pa := Pa) (X := X) (K := K) (L₀ := L₀) (δ₁ := δ₁)
    (s := c5 * Pa.N ^ (1 - δ₁)) (u := fun z => betaL Pa q p φ z0 Lm z) (v := E)
    hX hK1 hδ₁pos hsnn hhypB
  have hT2 := hHigh (Pa := Pa) (X := X) (K := K) (L₀ := L₀) (φ := φ) (z0 := z0)
    (β := β) (ε := fun _ => 1) δ₁ hX hK1 hδ₁pos hδ₁lt hβ (fun z => by norm_num) hcaps.1 hcaps.2
  have hT3 := hEng hβ hX K hK1
  have hT4 := hGuard hβ X K (fun _ => 1) hX hKu hX9 hε1 hcaps.1 hcaps.2
  -- ### the pure arithmetic
  have hnum := hNum (N := Pa.N) (X := (X : ℝ)) (Lm := (Lm : ℝ)) (K := K) (L₀ := L₀)
    (θ := Pa.θ) (Pz := (Pa.Pz : ℝ)) (UB := (uniB Pa : ℝ))
    (E2v := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
    (Ev := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2)
    hN₀_le hN3 hX1 hθ0 hθ1 hX8 hXcap hPz0 (by exact_mod_cast hK1) hKg hKu
    hL₀le hLm1r hLmLog hUB hUB4 hE2nn hE2' hEvnn hEv
  -- ### the four §17 identities
  have hW1 : WUni6 Pa X β = WUniOmega6Pull6 Pa X β := WUni6_eq_WUniOmega6Pull6 Pa X φ z0 β hβ hX
  have hMoll : WUniOmega6Pull6Moll Pa X β K = uniModeSum Pa X β K (fun _ => 1) :=
    WUniOmega6Pull6Moll_eq_uniModeSum hβ hε1 X K
  have hFree : uniModeSumFree Pa X β K (fun _ => 1)
      = WUniOmega6Pull6Char Pa X β K (fun _ => 1) :=
    uniModeSumFree_eq_WUniOmega6Pull6Char Pa X β K (fun _ => 1)
  have hreg := WUniOmega6Pull6Char_eq_regions6b Pa X K L₀ δ₁ β (fun _ => 1)
  have hsplit'' : WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K (fun _ => 1)
      = (WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Moll Pa X β K)
        + (uniModeSum Pa X β K (fun _ => 1) - uniModeSumFree Pa X β K (fun _ => 1)) := by
    rw [hW1, hMoll, hFree]; ring
  have hβuE : β = (fun z => betaL Pa q p φ z0 Lm z) + E := by
    funext z
    simp only [Pi.add_apply, hEdef]
    ring
  have hLowSplit : ‖charRegionLow6 Pa X K L₀ δ₁ β (fun _ => 1)‖
      ≤ ‖charRegionLow6 Pa X K L₀ δ₁ (fun z => betaL Pa q p φ z0 Lm z) (fun _ => 1)‖
        + ‖charRegionLow6 Pa X K L₀ δ₁ E (fun _ => 1)‖
        + C_X * (Real.log ((K : ℝ) + 2)) ^ 2
            * ((X : ℝ) * (1 + Real.log ((uniB Pa : ℝ) + 2)))
            * (c5 * Pa.N ^ (1 - δ₁))
            * Real.sqrt (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2)
            * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
    rw [hβuE]; exact hT6
  have h3 : ‖WUni6 Pa X β‖
      ≤ ‖WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K (fun _ => 1)‖
        + ‖WUniOmega6Pull6Char Pa X β K (fun _ => 1)‖ := by
    rw [show ‖WUni6 Pa X β‖ = ‖(WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K (fun _ => 1))
        + WUniOmega6Pull6Char Pa X β K (fun _ => 1)‖ from by rw [sub_add_cancel]]
    exact norm_add_le _ _
  have h1 : ‖WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K (fun _ => 1)‖
      ≤ ‖WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Moll Pa X β K‖
        + ‖uniModeSum Pa X β K (fun _ => 1) - uniModeSumFree Pa X β K (fun _ => 1)‖ := by
    rw [hsplit'']; exact norm_add_le _ _
  have h2 : ‖WUniOmega6Pull6Char Pa X β K (fun _ => 1)‖
      ≤ ‖charRegionLow6 Pa X K L₀ δ₁ β (fun _ => 1)‖
        + ‖charRegionHigh6 Pa X K L₀ δ₁ β (fun _ => 1)‖ := by
    rw [hreg]; exact norm_add_le _ _
  have hchain6 : ‖WUni6 Pa X β‖
      ≤ C_L * c5 ^ 2 * Pa.N ^ (2 - 2 * δ₁) * (Real.log ((K : ℝ) + 2)) ^ 2
            * ((X : ℝ) * Real.sqrt (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1)
                + (Pa.N ^ δ₁ / (2 * (K : ℝ) + (L₀ : ℝ) + 2) + 1) ^ ((3 : ℝ) / 2))
        + C_H * (1 + Clat)
            * (1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3)
            * (Real.log ((K : ℝ) + 2)) ^ 2
            * ((X : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * Pa.N ^ (1 - δ₁)
                + (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2))
        + C_E * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4
            * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) / (K : ℝ)
        + C_G * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log (Pa.N + 2)
        + C_P * (Real.log ((K : ℝ) + 2)) ^ 2
            * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2)
            * (Pa.N * Real.log ((X : ℝ) + 2) + (X : ℝ) ^ 2 * Pa.N ^ δ₁)
        + C_X * (Real.log ((K : ℝ) + 2)) ^ 2 * (X : ℝ)
            * (1 + Real.log ((uniB Pa : ℝ) + 2)) * (c5 * Pa.N ^ (1 - δ₁))
            * Real.sqrt (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖E z‖ ^ 2)
            * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
    have hlow := hLowSplit
    have h1' := h1
    have h2' := h2
    have h2s := hT2
    have h3s := hT3
    have h4s := hT4
    have hT1s := hT1
    have hT5s := hT5
    linarith only [h3, h1', h2', hlow, hT1s, hT5s, h2s, h3s, h4s]
  refine le_trans hchain6 (le_trans hnum ?_)
  have hnn : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
    mul_nonneg (mul_nonneg (add_nonneg hPz1 hXinv0) (by positivity)) hLnn
  have hfin : cN * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ max (2 * Cs + Cst) cN * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (2 * Cs + Cst) cN) hnn
    linarith only [h]
  exact hfin

/-! ## 3. The amended contract `Area7_6b` from the uniform cut and the strip -/

/-- **`Work.FITop4.Area7_6b` from `Area7Uni6B` and the strip bound.**  The same reduction as
`Work.FIArea7.area7_6_of_uniform_of_strip`, with the two amended hypotheses of the contract
(`Pa.τ` pinned, axis-free polar box) threaded into `Area7Uni6B`.  The strip bound
`Area7Strip6` is proved for *all* `IsBetaCoeff6` coefficients, so it is unchanged. -/
theorem area7_6b_of_uniform_of_strip (hU : Area7Uni6B) (hS : Area7Strip6) :
    Work.FITop4.Area7_6b := by
  intro η hη0 hηlt
  obtain ⟨δ, c, xU, hδ, hc, hU⟩ := hU η hη0 hηlt
  obtain ⟨C, xS, hC, hS⟩ := hS
  refine ⟨min δ ((1 : ℝ) / 9), c + C, max xU xS, lt_min hδ (by norm_num),
    by positivity, ?_⟩
  intro Pa hx hηPa hτ X φ z0 β hβ hfar hX hXδ hXcap
  have hxU' : xU ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hxS' : xS ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hNpos : (0 : ℝ) < Pa.N := by linarith only [Pa.hN1]
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hδ' : (X : ℝ) < Pa.N ^ δ :=
    lt_of_lt_of_le hXδ (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  have h9 : (X : ℝ) ^ 9 ≤ Pa.N := by
    have hXle : (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) :=
      le_of_lt (lt_of_lt_of_le hXδ
        (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)))
    have h9' : (Pa.N ^ ((1 : ℝ) / 9)) ^ 9 = Pa.N := by
      rw [← Real.rpow_natCast (Pa.N ^ ((1 : ℝ) / 9)) 9, ← Real.rpow_mul hNpos.le]
      norm_num
    calc (X : ℝ) ^ 9 ≤ (Pa.N ^ ((1 : ℝ) / 9)) ^ 9 :=
          pow_le_pow_left₀ (by positivity) hXle 9
      _ = Pa.N := h9'
  have h1 := hU Pa hxU' hηPa hτ X φ z0 β hβ hfar hX hδ' hXcap
  have h2 := hS Pa hxS' X φ z0 β hβ hX h9
  have hRnn : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
    have hPpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
      have h : (0 : ℕ) < Pa.Pz := lt_of_lt_of_le Nat.zero_lt_two Pa.hP2
      exact_mod_cast h
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have h : (0 : ℕ) < X := lt_of_lt_of_le Nat.zero_lt_one hX
      exact_mod_cast h
    exact mul_nonneg (mul_nonneg
      (add_nonneg (inv_nonneg.mpr hPpos.le) (inv_nonneg.mpr hXpos.le))
      (sq_nonneg _)) (Real.log_nonneg hN1)
  calc ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      = ‖WUni6 Pa X β - Strip6 Pa X β‖ := by
        rw [Wcut6_add_Bcut6_eq_WUni6_sub_Strip6]
    _ ≤ ‖WUni6 Pa X β‖ + ‖Strip6 Pa X β‖ := norm_sub_le _ _
    _ ≤ c * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          + C * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
        add_le_add h1 h2
    _ = (c + C) * ((Pa.Pz : ℝ)⁻¹ + ((X : ℝ))⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by ring

end

end Work.FIArea7
