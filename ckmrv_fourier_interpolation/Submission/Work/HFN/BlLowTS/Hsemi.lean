import Mathlib
import Submission.Work.HFN.BlLowTS.Base
import Submission.Work.Asymptotics.BlLow.PhiSpike
import Submission.Work.HFN.HalfFunnel.lowRegion_badLine

/-!
# The `r`-seminorm bound for the low bad-line layer `lowF2` on `blLowSet`

This file is the `blLowSet` analogue of the assembly in
`Submission/Work/Asymptotics/HalfFunnel/lowRegion_badLine.lean`: the spike-removed explicit layer
`HalfFunnel.lowF2` has bounded `r`-seminorms on the low bad-line region
`blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`.

The five analytic inputs are

* the pointwise decomposition `‖K - tpole‖ ≤ C` on the window (`BlLow.window_bound`),
* the off-window bound `‖K‖ ≤ C` (`BlLow.offwindow_bound`),
* the cusp-`i∞` expansion `K = Aexp (Gcusp ℓ d) + O((1+t)^M e^{-πt})` (`BlLow.blLow_Aexp_tail`),
* the explicit spike integral (`BlLow.blLow_PhiSpike_deriv`),
* the spike-removed amplitudes (`BlLow.blLow_Phi12_deriv`),

glued by the region-generic argument of `HalfFunnel.lowBad_hsemi_of_bounds`.
-/

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.BlLowTS
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel
open Work.Kernels

/-! ## The `r`-seminorm bound for the `high` piece on `blLowSet` -/

theorem blLow_highPart_seminorm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), Work.Asymptotics.BlLow.blLowSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ ≤ C := by
  obtain ⟨c, N, hc, hb⟩ := highPart_seminorm_scaled (Gcusp ℓ d) (fun i j => Gcusp_moderate ℓ d i j) k l
  refine ⟨c * max (6 ^ N) 1, mul_nonneg hc (le_trans zero_le_one (le_max_right _ _)), ?_⟩
  intro τ r hτ
  have hs6 : scale τ ≤ 6 := Work.HFN.BlLow.scale_le_six hτ
  have hs1 : (1:ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  have hbound : (scale τ) ^ N ≤ max (6 ^ N) 1 := by
    rcases le_or_gt 0 N with hN | hN
    · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one hs1) hs6 hN) (le_max_left _ _)
    · have h2 : (scale τ) ^ N ≤ (1:ℝ) ^ N := Real.rpow_le_rpow_of_nonpos (by norm_num) hs1 (le_of_lt hN)
      rw [Real.one_rpow] at h2
      exact h2.trans (le_max_right _ _)
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖
      ≤ c * (scale τ) ^ N := hb τ r hτ.1
    _ ≤ c * max (6 ^ N) 1 := mul_le_mul_of_nonneg_left hbound hc

/-! ## Smoothness of the spike piece -/

lemma contDiffOn_PhiSpike {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiSpike τ x) (Set.Ioi (-1)) := by
  set a : ℝ := τ.im - lowRho with ha
  set b : ℝ := τ.im + lowRho with hb
  have hapos : 0 < a := by rw [ha, lowRho]; linarith [hτ.2.1]
  have hab : a ≤ b := by rw [ha, hb, lowRho]; linarith
  have hcnt : Continuous (fun t : ℝ => tpole τ t) := blLow_continuous_tpole hτ
  have hmeas : AEStronglyMeasurable (fun t : ℝ => tpole τ t)
      (volume.restrict (Set.Ioc a b)) := hcnt.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * |τ.re - tsign τ|) :=
    Filter.Eventually.of_forall (fun t => blLow_norm_tpole_le hτ t)
  have hkey := contDiffOn_intervalIntegral_exp_ofReal_general (κ := fun t => tpole τ t)
    hapos hab (by positivity) hmeas hbound
  have hid : ∀ x : ℝ, PhiSpike τ x
      = ∫ t in (a)..(b), tpole τ t * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiSpike, lowWin, ← ha, ← hb]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab]
  exact hkey.congr (fun x _ => hid x)

/-! ## Smoothness of the low and tail pieces -/

lemma contDiffOn_PhiOne (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiOne ℓ d τ x) (Set.Ioi (-1)) := by
  have hLT : (1:ℝ) ≤ lowT := by rw [lowT]; norm_num
  have hmeas1 : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc 0 1)) := (measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => (lowWin τ).indicator (tpole τ) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    ((blLow_continuous_tpole hτ).measurable.indicator measurableSet_Ioo).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)),
      ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Set.mem_Ioc] at ht
    by_cases htw : t ∈ lowWin τ
    · rw [Set.indicator_of_mem htw]
      exact hdec1 τ hτ t ht.1 (le_trans ht.2 hLT)
    · rw [Set.indicator_of_notMem htw, sub_zero]
      exact hdec2 τ hτ t ht.1 (le_trans ht.2 hLT) (blLow_off_win_gives_sep htw)
  have hkey := contDiffOn_intervalIntegral_exp_ofReal (κ := fun t : ℝ =>
    Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) hC (hmeas1.sub hmeas2) hbound
  have hid : ∀ x : ℝ, PhiOne ℓ d τ x
      = ∫ t in (0:ℝ)..1, (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
          * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiOne, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hkey.congr (fun x _ => hid x)

lemma tpole_not_mem_win {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) {t : ℝ}
    (ht : lowT ≤ t) : t ∉ lowWin τ := by
  intro h
  rw [lowWin, Set.mem_Ioo] at h
  rw [lowT] at ht
  have h1 : τ.im + lowRho < 3 := by
    rw [lowRho]
    linarith [hτ.2.2.1]
  linarith [h.2, h1, ht]

lemma contDiffOn_PhiTwo (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiTwo ℓ d τ x) (Set.Ioi (-1)) := by
  obtain ⟨CB, hCB, hbC⟩ := blLow_Aexp_le ℓ d hd
  obtain ⟨Ct, Mt, hCt, hMt, hbT⟩ := htail
  have hLT : (1:ℝ) ≤ lowT := by rw [lowT]; norm_num
  set D : ℝ := max ((C + CB + 1) * Real.exp (Real.pi * lowT)) (Ct * 2 ^ Mt) with hD
  set M : ℝ := max Mt 0 with hM
  have hDpos : 0 < D := by
    have h1 : (0:ℝ) < (C + CB + 1) * Real.exp (Real.pi * lowT) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have hMnn : 0 ≤ M := le_max_right _ _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t
      - Aexp (Gcusp ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
      (volume.restrict (Set.Ici 1)) :=
    (((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      (by unfold Aexp; fun_prop)).sub
      (((blLow_continuous_tpole hτ).measurable.indicator measurableSet_Ioo).aestronglyMeasurable)
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)),
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
        - (lowWin τ).indicator (tpole τ) t‖ ≤ D * t ^ M * Real.exp (-(Real.pi * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1:ℝ) ≤ t := ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    by_cases htT : t ≤ lowT
    · have h1 : ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖ ≤ C := by
        by_cases hw : t ∈ lowWin τ
        · rw [Set.indicator_of_mem hw]
          exact hdec1 τ hτ t ht0 (le_trans htT (le_refl lowT))
        · rw [Set.indicator_of_notMem hw, sub_zero]
          exact hdec2 τ hτ t ht0 (le_trans htT (le_refl lowT)) (blLow_off_win_gives_sep hw)
      have h2 : ‖Aexp (Gcusp ℓ d) τ t‖ ≤ CB := hbC τ hτ t ht1 htT
      have h3 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
          - (lowWin τ).indicator (tpole τ) t‖
          ≤ C + CB + 1 := by
        have heq : Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
            - (lowWin τ).indicator (tpole τ) t
            = (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
              - Aexp (Gcusp ℓ d) τ t := by ring
        rw [heq]
        linarith [norm_sub_le (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
          (Aexp (Gcusp ℓ d) τ t)]
      have h4 : t ^ M * Real.exp (-(Real.pi * t)) ≥ Real.exp (-(Real.pi * lowT)) := by
        have h5 : (1:ℝ) ≤ t ^ M := Real.one_le_rpow ht1 hMnn
        have h6 : Real.exp (-(Real.pi * lowT)) ≤ Real.exp (-(Real.pi * t)) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htT])
        calc Real.exp (-(Real.pi * lowT)) ≤ Real.exp (-(Real.pi * t)) := h6
          _ = 1 * Real.exp (-(Real.pi * t)) := (one_mul _).symm
          _ ≤ t ^ M * Real.exp (-(Real.pi * t)) :=
              mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
      have h7 : (C + CB + 1) ≤ D * Real.exp (-(Real.pi * lowT)) := by
        have h8 : (C + CB + 1) * Real.exp (Real.pi * lowT) ≤ D := le_max_left _ _
        have h9 : ((C + CB + 1) * Real.exp (Real.pi * lowT)) * Real.exp (-(Real.pi * lowT))
            = (C + CB + 1) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-(Real.pi * lowT))).le
        rw [h9] at h10
        linarith [h10]
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
            - (lowWin τ).indicator (tpole τ) t‖
          ≤ C + CB + 1 := h3
        _ ≤ D * (t ^ M * Real.exp (-(Real.pi * t))) := by
            have h11 : D * Real.exp (-(Real.pi * lowT)) ≤ D * (t ^ M * Real.exp (-(Real.pi * t))) :=
              mul_le_mul_of_nonneg_left h4 hDpos.le
            linarith [h7, h11]
        _ = D * t ^ M * Real.exp (-(Real.pi * t)) := by ring
    · have htT' : lowT ≤ t := le_of_lt (not_le.mp htT)
      rw [Set.indicator_of_notMem (tpole_not_mem_win hτ htT'), sub_zero]
      have h1 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)) := hbT τ hτ t htT'
      have h2 : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
        have h3 : (1 + t) ≤ 2 * t := by linarith
        calc (1 + t) ^ Mt ≤ (2 * t) ^ Mt := Real.rpow_le_rpow (by linarith) h3 hMt
          _ = 2 ^ Mt * t ^ Mt := Real.mul_rpow (by norm_num) (by linarith)
      have h4 : t ^ Mt ≤ t ^ M := Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left Mt 0)
      have h5 : Ct * 2 ^ Mt ≤ D := le_max_right _ _
      have h6 : Ct * (1 + t) ^ Mt ≤ D * t ^ M := by
        calc Ct * (1 + t) ^ Mt ≤ Ct * (2 ^ Mt * t ^ Mt) := mul_le_mul_of_nonneg_left h2 hCt.le
          _ = (Ct * 2 ^ Mt) * t ^ Mt := by ring
          _ ≤ D * t ^ Mt := mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg (by linarith) _)
          _ ≤ D * t ^ M := mul_le_mul_of_nonneg_left h4 (le_of_lt hDpos)
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)) := h1
        _ = (Ct * (1 + t) ^ Mt) * Real.exp (-(Real.pi * t)) := by ring
        _ ≤ (D * t ^ M) * Real.exp (-(Real.pi * t)) :=
            mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
        _ = D * t ^ M * Real.exp (-(Real.pi * t)) := by ring
  have hkey := contDiffOn_integral_Ici_exp_ofReal (ψ := fun t : ℝ => Kaxis (Kfun ℓ d) τ t
    - Aexp (Gcusp ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) hDpos hMnn hmeas hbound
  have hid : ∀ x : ℝ, PhiTwo ℓ d τ x
      = ∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
          - (lowWin τ).indicator (tpole τ) t) * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiTwo]
  exact hkey.congr (fun x _ => hid x)

lemma contDiffOn_part (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x)
      (Set.Ioi (-1)) :=
  ((contDiffOn_PhiOne ℓ d hd hC hdec1 hdec2 hτ).add
    (contDiffOn_PhiTwo ℓ d hd hC hdec1 hdec2 htail hτ)).add (contDiffOn_PhiSpike hτ)

/-! ## The `r`-seminorm bound for `lowF2` on `blLowSet` -/

theorem blLow_hsemi_of_bounds (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cdec)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    (hPhiSpike : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖ ≤ K * (1 + x) ^ (-(N : ℝ)))
    (hPhi12 : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)))
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), Work.Asymptotics.BlLow.blLowSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => lowF2 ℓ d τ s) r‖ ≤ C := by
  obtain ⟨Chp, hChp, hhpb⟩ := blLow_highPart_seminorm ℓ d hd k l
  obtain ⟨c, hc, hcomp⟩ := exists_seminorm_bound_of_iteratedDeriv_bound_poly k l (k + l) (by omega)
  set N : ℝ := ((k + l : ℕ) : ℝ) with hN
  have hmn : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (m ≤ l →
      ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x‖
          ≤ K * (1 + x) ^ (-N)) := by
    intro m
    by_cases hm : m ≤ l
    · obtain ⟨K1, hK1, hb1⟩ := hPhi12 m (k + l)
      obtain ⟨K2, hK2, hb2⟩ := hPhiSpike m (k + l)
      refine ⟨K1 + K2, by positivity, fun _ τ hτ x hx => ?_⟩
      have hxm : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
      have hnhds : Set.Ioi (-1) ∈ 𝓝 x := IsOpen.mem_nhds isOpen_Ioi hxm
      have hd1 : ContDiffAt ℝ (m : ℕ∞) (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x :=
        ((contDiffOn_PhiOne ℓ d hd hCdec hdec1 hdec2 hτ).add
          (contDiffOn_PhiTwo ℓ d hd hCdec hdec1 hdec2 htail hτ)).contDiffAt hnhds |>.of_le le_top
      have hd2 : ContDiffAt ℝ (m : ℕ∞) (fun x : ℝ => PhiSpike τ x) x :=
        (contDiffOn_PhiSpike hτ).contDiffAt hnhds |>.of_le le_top
      have hid : iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x
          = iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x
            + iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x := by
        rw [show (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x)
            = (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) + (fun x : ℝ => PhiSpike τ x)
            from rfl]
        exact iteratedDeriv_add hd1 hd2
      rw [hid, hN]
      calc ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x
            + iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖
          ≤ ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x‖
            + ‖iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖ := norm_add_le _ _
        _ ≤ K1 * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) + K2 * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) :=
            add_le_add (hb1 τ hτ x hx) (hb2 τ hτ x hx)
        _ = (K1 + K2) * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) := by ring
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose Kf hKf using hmn
  set Ktot : ℝ := ∑ m ∈ Finset.range (l + 1), Kf m with hKtot
  have hKf0 : ∀ m, 0 ≤ Kf m := fun m => (hKf m).1
  have hKtot0 : 0 ≤ Ktot := Finset.sum_nonneg (fun m _ => hKf0 m)
  have hKtotb : ∀ m : ℕ, m ≤ l → ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x‖
        ≤ Ktot * (1 + x) ^ (-N) := by
    intro m hm τ hτ x hx
    have hmem : m ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h := (hKf m).2 hm τ hτ x hx
    have hle : Kf m ≤ Ktot := Finset.single_le_sum (fun i _ => hKf0 i) hmem
    have hpow : 0 ≤ (1 + x) ^ (-N) := Real.rpow_nonneg (by linarith) _
    exact le_trans h (mul_le_mul_of_nonneg_right hle hpow)
  refine ⟨Chp + c * Ktot, by positivity, fun τ r hτ => ?_⟩
  have hFdiff : ContDiffOn ℝ (l : ℕ∞)
      (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) (Set.Ioi (-1)) :=
    (contDiffOn_part ℓ d hd hCdec hdec1 hdec2 htail hτ).of_le le_top
  have hb := hcomp (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) Ktot hKtot0
    hFdiff (fun m hm x hx => hKtotb m hm τ hτ x hx) r
  have hhs : iteratedDeriv l (fun s : ℝ => lowF2 ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r
        + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r := by
    rw [show (fun s : ℝ => lowF2 ℓ d τ s)
        = (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2)))
          + (fun s : ℝ => highPart (Gcusp ℓ d) τ s) from rfl]
    refine iteratedDeriv_add ?_ ?_
    · have hFn : ContDiffAt ℝ ω
          (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) (r ^ 2) :=
        (contDiffOn_part ℓ d hd hCdec hdec1 hdec2 htail hτ).contDiffAt
          (IsOpen.mem_nhds isOpen_Ioi (by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]))
      have hcomp2 : ContDiffAt ℝ ω (fun s : ℝ =>
          PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2)) r := by
        have hpow : ContDiffAt ℝ ω (fun s : ℝ => s ^ 2) r := by fun_prop
        have hc := ContDiffAt.comp (f := fun s : ℝ => s ^ 2)
          (g := fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) r hFn hpow
        exact hc
      have hcos : ContDiffAt ℝ ω (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)) r := by
        have h1 : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ))
            = fun s : ℝ => sinSq s := by
          funext s
          rw [sinSq_eq_two_sub_two_cos]
          push_cast
          ring
        rw [h1]
        exact contDiff_omega_sinSq.contDiffAt
      exact (hcos.mul hcomp2).of_le le_top
    · exact ((contDiff_omega_highPart (Gcusp ℓ d) τ).contDiffAt).of_le le_top
  rw [hhs]
  have h2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ ≤ Chp :=
    hhpb τ r hτ
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
            * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r
        + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r‖
          + ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ := by ring
    _ ≤ c * Ktot + Chp := by linarith
    _ = Chp + c * Ktot := by ring

/-! ## Evenness and smoothness of `lowF2` in the radial variable -/

lemma lowF2_neg_blLow (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    lowF2 ℓ d τ (-r) = lowF2 ℓ d τ r := by
  simp only [lowF2, neg_sq, highPart]

lemma contDiff_lowF2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      lowRho ≤ |t - τ.im| → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ →
      ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    ContDiff ℝ ω (fun r : ℝ => lowF2 ℓ d τ r) := by
  have hpart := contDiffOn_part ℓ d hd hC hdec1 hdec2 htail hτ
  have hcomp : ContDiff ℝ ω (fun r : ℝ =>
      PhiOne ℓ d τ (r ^ 2) + PhiTwo ℓ d τ (r ^ 2) + PhiSpike τ (r ^ 2)) := by
    have h := hpart.comp_contDiff (n := ω) (f := fun r : ℝ => r ^ 2) (by fun_prop)
      (fun r => by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r])
    simpa [Function.comp_def] using h
  have hcos : ContDiff ℝ ω (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) := by
    have h1 : (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) = fun r : ℝ => sinSq r := by
      funext r
      rw [sinSq_eq_two_sub_two_cos]
      push_cast
      ring
    rw [h1]
    exact contDiff_omega_sinSq
  have hhigh : ContDiff ℝ ω (fun r : ℝ => highPart (Gcusp ℓ d) τ r) :=
    contDiff_omega_highPart (Gcusp ℓ d) τ
  simpa [lowF2] using (hcos.mul hcomp).add hhigh

end Work.HFN.BlLowTS
