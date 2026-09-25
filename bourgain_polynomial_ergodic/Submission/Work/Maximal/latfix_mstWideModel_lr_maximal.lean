import Mathlib
import Submission.Work.Maximal.mstWideModel_lr_maximal
import Submission.Work.Maximal.latfix_wideLat_class_bound
import Submission.Work.Maximal.latfix_mstWideModel_lr_large
import Submission.Work.Maximal.latfix_wideModel_small_s_bound

open MeasureTheory Finset
open Work.BourgainPlan.IonescuWainger Work.BourgainPlan.Maximal Work.Maximal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

theorem mstWideModel_lr_maximal_lat (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hϱml : ∀ s : ℕ, MeasureTheory.MemLp (Work.Maximal.mstWideBump P χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (Work.Maximal.mstWideModel P l χ η k s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    (hLattice : ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H →
      MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.Maximal.mstWideModelCls P l χ η k s (hΩml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  classical
  obtain ⟨C_lat, hC_lat_pos, hlattice⟩ := hLattice
  obtain ⟨K, hKpos, Tc, hTc⟩ := mstMS_curve_neg_le_hlMax P hd
  obtain ⟨s₀, hs₀⟩ := mstTorsion l hl
  obtain ⟨B_card, hB_card_pos, hcard⟩ := mstU_card_le_exp l hl
  obtain ⟨C_ϱop, hC_ϱop_pos, hϱop⟩ :=
    wideBump_op_lr_bound P χ η M hM hηc hηbd hder1 hder2 hηsup hϱml hr
  obtain ⟨C_pig, hC_pig_pos, hPiG⟩ :=
    mstWidePiG_lr_bound P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hr hr2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hηsup' : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hTc0 : (0:ℝ) ≤ (Tc.card : ℝ) := Nat.cast_nonneg _
  set CL : ℝ := (K + (Tc.card : ℝ) + C_lat + C_pig + 1) ^ 6 with hCL
  have hCL0 : 0 ≤ CL := by rw [hCL]; positivity
  set Bcs : ℝ := B_card * Real.exp ((s₀ : ℝ) ^ (1 / 10 : ℝ)) with hBcs
  have hBcs0 : 0 ≤ Bcs := by rw [hBcs]; positivity
  set CS : ℝ := (Bcs + K + (Tc.card : ℝ) + C_lat + C_ϱop + 1) ^ 6 with hCS
  have hCS0 : 0 ≤ CS := by rw [hCS]; positivity
  have hCLle : CL ≤ max CL (CS / Real.log 2) + 1 := by
    linarith [le_max_left CL (CS / Real.log 2)]
  have hCSle : CS ≤ (max CL (CS / Real.log 2) + 1) * Real.log 2 := by
    have h1 : CS / Real.log 2 ≤ max CL (CS / Real.log 2) + 1 := by
      linarith [le_max_right CL (CS / Real.log 2)]
    calc CS = (CS / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (max CL (CS / Real.log 2) + 1) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1 hlog2.le
  have hCpos : 0 < max CL (CS / Real.log 2) + 1 := by
    have h := le_max_left CL (CS / Real.log 2)
    linarith
  refine ⟨max CL (CS / Real.log 2) + 1, hCpos, fun s g => ?_⟩
  have hlogpos : 0 < Real.log ((s : ℝ) + 2) := by
    apply Real.log_pos
    have : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
    linarith
  have hlog2le : Real.log 2 ≤ Real.log ((s:ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
  have hgoal : ∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
        (memℓp_finsupp g) n‖ₑ) ^ r ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r
        * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
    by_cases hs : s₀ ≤ s
    · -- ================= the large scales =================
      have hQE : ∀ β ∈ mstAnnulus l s, fourier (((mstQ' s : ℕ)) : ℤ) β = 1 := by
        intro β hβ
        have hmem : β ∈ mstU l (s + 1) := by
          have h1 : β ∈ mstLevel l (s + 1) := (Finset.mem_sdiff.mp hβ).1
          rwa [mstLevel_succ] at h1
        exact hs₀ s hs β hmem
      have hlarge := mstWideModel_lr_large_lat P hd l (χ := χ) η hηc hηsup hϱml hΩml hr hr2
        K hKpos Tc hTc C_lat hC_lat_pos hlattice C_pig hC_pig_pos hPiG s hQE g
      have hrpow : (K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)
            * (C_pig * Real.log ((s:ℝ)+2)) ^ r
          ≤ ((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r := by
        have hstep1 : K ^ r * (Tc.card : ℝ) ^ r * (Tc.card : ℝ) * C_lat ^ r * C_pig ^ r
            ≤ CL ^ r := by
          have h := rpow_absorb (r := r) (by linarith : (1:ℝ) ≤ r) (a := K)
            (b := (Tc.card : ℝ)) (c := C_lat) (d := C_pig) (e := 0)
            hKpos.le hTc0 hC_lat_pos.le hC_pig_pos.le (by norm_num)
          rw [show K + (Tc.card : ℝ) + C_lat + C_pig + 0 + 1
            = K + (Tc.card : ℝ) + C_lat + C_pig + 1 from by ring] at h
          rw [hCL]
          exact h
        have hmul1 : K ^ r * (Tc.card : ℝ) ^ r * (Tc.card : ℝ) * C_lat ^ r * C_pig ^ r
              * Real.log ((s:ℝ)+2) ^ r ≤ CL ^ r * Real.log ((s:ℝ)+2) ^ r :=
          mul_le_mul_of_nonneg_right hstep1 (Real.rpow_nonneg hlogpos.le r)
        have hfin : CL ^ r * Real.log ((s:ℝ)+2) ^ r
            ≤ ((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r := by
          rw [← Real.mul_rpow hCL0 hlogpos.le]
          exact Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_right hCLle hlogpos.le) (by linarith : (0:ℝ) ≤ r)
        calc (K * (Tc.card : ℝ) * C_lat) ^ r * (Tc.card : ℝ)
              * (C_pig * Real.log ((s:ℝ)+2)) ^ r
            = (K ^ r * (Tc.card : ℝ) ^ r * (Tc.card : ℝ) * C_lat ^ r * C_pig ^ r)
                * Real.log ((s:ℝ)+2) ^ r := by
              rw [Real.mul_rpow (mul_nonneg hKpos.le hTc0) hC_lat_pos.le,
                Real.mul_rpow hKpos.le hTc0, Real.mul_rpow hC_pig_pos.le hlogpos.le]
              ring
          _ ≤ CL ^ r * Real.log ((s:ℝ)+2) ^ r := hmul1
          _ ≤ ((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r := hfin
      refine le_trans hlarge ?_
      refine mul_le_mul_left ?_ _
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCpos.le hlogpos.le)
        (by linarith : (0:ℝ) ≤ r)]
      exact ENNReal.ofReal_le_ofReal hrpow
    · -- ================= the small scales =================
      have hs' : s < s₀ := not_le.mp hs
      have hsmall := wideModel_small_s_bound_lat P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hηsup hϱml
        hΩml hr hr2 K hKpos Tc hTc C_lat hC_lat_pos hlattice C_ϱop hC_ϱop_pos hϱop s g
      have hcard_s : (((mstU l (s+1)).card : ℝ)) ≤ Bcs := by
        have h1 := hcard (s + 1)
        have h2 : ((((s + 1 : ℕ)) : ℝ) ^ l) ^ mstRho l = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
          rw [mstRho_pow_eq_real l hl (s + 1) (by omega)]
          push_cast
          ring
        rw [h2] at h1
        have h3 : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (s₀ : ℝ) ^ (1 / 10 : ℝ) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
          have : s + 1 ≤ s₀ := by omega
          exact_mod_cast this
        have h4 : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
            ≤ Real.exp ((s₀ : ℝ) ^ (1 / 10 : ℝ)) := Real.exp_le_exp.mpr h3
        calc (((mstU l (s+1)).card : ℝ))
            ≤ B_card * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := h1
          _ ≤ B_card * Real.exp ((s₀ : ℝ) ^ (1 / 10 : ℝ)) :=
              mul_le_mul_of_nonneg_left h4 hB_card_pos.le
          _ = Bcs := by rw [hBcs]
      have hZ : (((mstU l (s+1)).card : ℝ)) + K + (Tc.card : ℝ) + C_lat + C_ϱop + 1
          ≤ Bcs + K + (Tc.card : ℝ) + C_lat + C_ϱop + 1 := by linarith
      have h6 : ((((mstU l (s+1)).card : ℝ)) + K + (Tc.card : ℝ) + C_lat + C_ϱop + 1) ^ 6
          ≤ CS := by
        rw [hCS]
        exact pow_le_pow_left₀ (by positivity) hZ 6
      have hCs : CS ≤ (max CL (CS / Real.log 2) + 1) * Real.log ((s:ℝ) + 2) := by
        calc CS ≤ (max CL (CS / Real.log 2) + 1) * Real.log 2 := hCSle
          _ ≤ (max CL (CS / Real.log 2) + 1) * Real.log ((s:ℝ) + 2) :=
              mul_le_mul_of_nonneg_left hlog2le hCpos.le
      have hCsr : CS ^ r ≤ ((max CL (CS / Real.log 2) + 1) * Real.log ((s:ℝ) + 2)) ^ r :=
        Real.rpow_le_rpow hCS0 hCs (by linarith : (0:ℝ) ≤ r)
      calc ∫⁻ n : ℤ, (⨆ k : ℕ, ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g)
            (memℓp_finsupp g) n‖ₑ) ^ r ∂MeasureTheory.Measure.count
          ≤ (ENNReal.ofReal ((((mstU l (s+1)).card : ℝ) + K + (Tc.card : ℝ) + C_lat
              + C_ϱop + 1) ^ 6)) ^ r
              * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := hsmall
        _ ≤ (ENNReal.ofReal CS) ^ r
              * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
            refine mul_le_mul_left ?_ _
            exact ENNReal.monotone_rpow_of_nonneg (by linarith : (0:ℝ) ≤ r)
              (ENNReal.ofReal_le_ofReal h6)
        _ = ENNReal.ofReal (CS ^ r)
              * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
            rw [ENNReal.ofReal_rpow_of_nonneg hCS0 (by linarith : (0:ℝ) ≤ r)]
        _ ≤ ENNReal.ofReal (((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r)
              * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
            refine mul_le_mul_left ?_ _
            exact ENNReal.ofReal_le_ofReal hCsr
        _ = ENNReal.ofReal ((max CL (CS / Real.log 2) + 1) * Real.log ((s : ℝ) + 2)) ^ r
              * ∫⁻ n : ℤ, ‖(⇑g) n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
            rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCpos.le hlogpos.le)
              (by linarith : (0:ℝ) ≤ r)]
  exact eLpNorm_le_of_lintegral_rpow_le (by linarith : (0:ℝ) < r)
    (mul_nonneg hCpos.le hlogpos.le) hgoal

end

end Work.Maximal
