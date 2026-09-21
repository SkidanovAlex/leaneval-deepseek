import Mathlib
import Submission.Work.OddCurveB.Step2.GsclWide
import Submission.Work.OddVolterra.WinData.thetaM_state_lipschitz_ext

/-!
# The right-hand side difference of the linearised clamped equation, wide window `[1/4, 19/20]`

This is `Work.OddVolterra.Existence.rhs_diff` (`window_deriv_close_core.lean`) with the slope
window widened from `[7/10, 19/20]` to `[1/4, 19/20]`: the constant multiplying the integral term
becomes `19/20 - 1/4 = 7/10` (it was `19/20 - 7/10 = 1/4`), the `𝐆`-row estimate is the wide
`w_gscl_data`, and the `ΘM`-estimates (`thetaM_close_box`, `TW2_*`, `thetaM_deriv_close_of_KvecM`)
are already stated on the wide window.  All other arguments are unchanged.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open Work.OddVolterra
open Work.OddVolterra.Existence
open scoped Topology ContDiff Interval

noncomputable section

theorem w_rhs_diff (n : ℕ) (hn : 1 ≤ n) (Kc : ℝ) (hKc : 0 ≤ Kc) (CX : ℝ) (hCX : 0 ≤ CX)
    (hXscl : ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        ‖XsCl n h s - XsCl n 0 s‖ ≤ CX * δ) :
    ∃ Mrhs : ℝ, 0 ≤ Mrhs ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      Kc * δ ≤ 9 / 20 →
      ∀ Z : ℝ → St, ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20)) →
      (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), dist (Z s) (baseState s) ≤ Kc * δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        ‖(- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
          - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)‖
          ≤ Mrhs * δ := by
  obtain ⟨Cgs, hCgsnn, hGscl⟩ := Work.OddCurveB.Step2.w_gscl_data n hn
  obtain ⟨CTh, hCThpos, hTclc⟩ := WinData.thetaM_close_box n hn (a := 1 / 4) (b := 1)
    (ρ := 9 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨MTh, BTh, hMThnn, hBThnn, hTcls⟩ :=
    Work.OddVolterra.WinData.thetaM_state_lipschitz_ext n hn
  obtain ⟨CD, LD, hCDpos, hLDpos, hTder⟩ :=
    WinData.thetaM_deriv_close_of_KvecM n hn (WinData.KvecM_deriv2_ext n hn)
  refine ⟨(Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((7 / 10) * (LD * Kc + CD)) + CX + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Cgs * Kc := mul_nonneg hCgsnn hKc
    have h2 : 0 ≤ MTh * Kc := mul_nonneg hMThnn hKc
    have h3 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
    have h4 : 0 ≤ (7 / 10) * (LD * Kc + CD) := by
      have h5 : 0 ≤ LD * Kc + CD := by linarith [h3, hCDpos.le]
      positivity
    linarith [h1, h2, h3, h4, hCgsnn, hCThpos.le, hCDpos.le, hCX]
  · intro h δ hh hδpos hδ100 hjet hsupp hKc9 Z hZc hZdist s hs
    have hδnn : 0 ≤ δ := hδpos.le
    have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
      fun k hk x => le_trans (hjet k (by omega) x) hδ100
    have hδ2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ :=
      fun k hk x => hjet k (by omega) x
    have hδn2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ :=
      fun k hk x => hjet k (by omega) x
    have h100n2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
      fun k hk x => le_trans (hjet k (by omega) x) hδ100
    have hZm : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ‖Z u - baseState u‖ ≤ 9 / 20 := by
      intro u hu
      have h1 := hZdist u hu
      rw [dist_eq_norm] at h1
      linarith [hKc9]
    have hZm9 : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        Z u ∈ Metric.closedBall (baseState u) (9 / 20) :=
      fun u hu => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hZm u hu
    have hbm : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        baseState u ∈ Metric.closedBall (baseState u) (9 / 20) :=
      fun u _ => Metric.mem_closedBall_self (by norm_num)
    have hW : s ∈ Set.Icc WinData.wLo WinData.wHi := by
      rw [WinData.wLo, WinData.wHi]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htwice : ‖Z s - baseState s‖ ≤ Kc * δ := by
      have h1 := hZdist s hs; rwa [dist_eq_norm] at h1
    -- term 1: the state datum
    have hterm1 : ‖GsCl n h s (Z s) - GsCl n 0 s (baseState s)‖ ≤ (Cgs * Kc + Cgs) * δ := by
      have hA := (hGscl h δ hh hδpos hδ100 hsupp hδ2 s hs (Z s) (hZm9 s hs)
        (baseState s) (hbm s hs))
      have hB := (hGscl h δ hh hδpos hδ100 hsupp hδ2 s hs (baseState s) (hbm s hs)
        (baseState s) (hbm s hs))
      have ht := dist_triangle (GsCl n h s (Z s)) (GsCl n h s (baseState s))
        (GsCl n 0 s (baseState s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      have hA2 : ‖GsCl n h s (Z s) - GsCl n h s (baseState s)‖ ≤ Cgs * ‖Z s - baseState s‖ := by
        have h := hA.2
        rwa [dist_eq_norm] at h
      have h2 : Cgs * ‖Z s - baseState s‖ ≤ Cgs * (Kc * δ) :=
        mul_le_mul_of_nonneg_left htwice hCgsnn
      nlinarith [ht, hA2, hB.1, h2, hCgsnn, hKc, hδnn]
    -- term 2: the diagonal datum
    have hterm2 : ‖WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)‖
        ≤ (MTh * Kc + CTh) * δ := by
      have hA := (hTcls h hh hsupp h100n2 s hs s hs (Z s) (hZm9 s hs))
      have hTcl1 : WinData.Tcl n h s s (Z s) = Work.OddVolterra.KernelExt.ThetaM n h s s (Z s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; linarith [hZm s hs])
      have hTcl0 : WinData.Tcl n 0 s s (baseState s) =
          Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; norm_num)
      have hTclb : WinData.Tcl n h s s (baseState s) =
          Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s) :=
        WinData.Tcl_eq_ThetaM hW hW
          (by rw [show WinData.wRho = (1 : ℝ) / 2 from rfl]; norm_num)
      have hB := hTclc h hh hsupp δ hδpos hδ100 hδn2 s ⟨hs.1, by linarith [hs.2]⟩ s
        ⟨hs.1, by linarith [hs.2]⟩ (baseState s) (hbm s hs)
      have ht := dist_triangle (Work.OddVolterra.KernelExt.ThetaM n h s s (Z s))
        (Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s))
        (Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      have h4 : ‖Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s) -
          Work.OddVolterra.KernelExt.ThetaM n 0 s s (baseState s)‖ ≤ CTh * δ := by
        rw [← dist_eq_norm]; exact hB
      have hA2 : ‖Work.OddVolterra.KernelExt.ThetaM n h s s (Z s) -
          Work.OddVolterra.KernelExt.ThetaM n h s s (baseState s)‖
          ≤ MTh * ‖Z s - baseState s‖ :=
        hA.2 (baseState s) (hbm s hs)
      have h2 : MTh * ‖Z s - baseState s‖ ≤ MTh * (Kc * δ) :=
        mul_le_mul_of_nonneg_left htwice hMThnn
      rw [hTcl1, hTcl0]
      nlinarith [ht, hA2, h4, h2, hMThnn, hCThpos.le, hKc, hδnn]
    -- term 3: the integral
    have hcontT : ContinuousOn (fun σ : ℝ => TsCl n h s σ (Z σ)) (Set.Icc s (19 / 20)) := by
      have hcurve : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc s (19 / 20)) :=
        continuousOn_const.prodMk (continuousOn_id.prodMk
          (hZc.mono (by intro x hx; exact ⟨le_trans hs.1 hx.1, hx.2⟩)))
      exact (tsCl_continuous (n := n) hn hh hsupp hsmall2).comp_continuousOn' hcurve
    have hI1 : IntervalIntegrable (fun σ : ℝ => TsCl n h s σ (Z σ)) volume s (19 / 20) :=
      hcontT.intervalIntegrable_of_Icc hs.2
    have hcontT0 : ContinuousOn (fun σ : ℝ => TsCl n 0 s σ (baseState σ)) (Set.Icc s (19 / 20)) := by
      have hcurve : ContinuousOn (fun σ : ℝ => (s, σ, baseState σ)) (Set.Icc s (19 / 20)) :=
        continuousOn_const.prodMk (continuousOn_id.prodMk
          (Work.OddVolterra.Existence.continuous_baseState.continuousOn.mono (Set.subset_univ _)))
      exact (tsCl_continuous (n := n) hn contDiff_const WDC.support_zero_wdc
        (WDC.hjet_zero_wdc (by norm_num))).comp_continuousOn' hcurve
    have hI2 : IntervalIntegrable (fun σ : ℝ => TsCl n 0 s σ (baseState σ)) volume s (19 / 20) :=
      hcontT0.intervalIntegrable_of_Icc hs.2
    have hpt : ∀ σ ∈ Set.Icc s (19 / 20),
        ‖TsCl n h s σ (Z σ) - TsCl n 0 s σ (baseState σ)‖ ≤ (LD * Kc + CD) * δ := by
      intro σ hσ
      have hσ9 : σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := ⟨le_trans hs.1 hσ.1, hσ.2⟩
      have hσW : σ ∈ Set.Icc WinData.wLo WinData.wHi := by
        rw [WinData.wLo, WinData.wHi]
        exact ⟨by linarith [hσ9.1], by linarith [hσ9.2]⟩
      have hZm9' : Z σ ∈ Metric.closedBall (baseState σ) (9 / 20) := hZm9 σ hσ9
      have hbm' : baseState σ ∈ Metric.closedBall (baseState σ) (9 / 20) := hbm σ hσ9
      have e1 : TsCl n h s σ (Z σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (Z σ)) s :=
        WDC.tsCl_eq_thetaM n hn hh hsupp hsmall2 hW hσW hZm9'
      have e2 : TsCl n h s σ (baseState σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (baseState σ)) s :=
        WDC.tsCl_eq_thetaM n hn hh hsupp hsmall2 hW hσW hbm'
      have e3 : TsCl n 0 s σ (baseState σ) =
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n 0 u σ (baseState σ)) s :=
        WDC.tsCl_eq_thetaM n hn contDiff_const WDC.support_zero_wdc
          (WDC.hjet_zero_wdc (by norm_num)) hW hσW hbm'
      have hA := (hTder h δ hh hδpos hδ100 hjet hsupp s ⟨by linarith [hs.1], hs.2⟩ σ
        ⟨by linarith [hσ9.1], by linarith [hσ.2]⟩ (Z σ) hZm9' (baseState σ) hbm')
      have hA0 := (hTder h δ hh hδpos hδ100 hjet hsupp s ⟨by linarith [hs.1], hs.2⟩ σ
        ⟨by linarith [hσ9.1], by linarith [hσ.2]⟩ (baseState σ) hbm' (baseState σ) hbm')
      have ht := dist_triangle (TsCl n h s σ (Z σ)) (TsCl n h s σ (baseState σ))
        (TsCl n 0 s σ (baseState σ))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      rw [e1, e2, e3] at ht
      rw [e1, e3]
      have hA2 : ‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (Z σ)) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ (baseState σ)) s‖
          ≤ LD * ‖Z σ - baseState σ‖ := hA.2
      have h2 : LD * ‖Z σ - baseState σ‖ ≤ LD * (Kc * δ) :=
        mul_le_mul_of_nonneg_left (by have h1 := hZdist σ hσ9; rwa [dist_eq_norm] at h1) hLDpos.le
      nlinarith [ht, hA2, hA0.1, h2, hLDpos.le, hCDpos.le, hKc, hδnn]
    have hterm3 : ‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
        ≤ ((7 / 10) * (LD * Kc + CD)) * δ := by
      rw [← intervalIntegral.integral_sub hI1 hI2]
      have hb : ∀ σ ∈ Set.uIoc s (19 / 20),
          ‖TsCl n h s σ (Z σ) - TsCl n 0 s σ (baseState σ)‖ ≤ (LD * Kc + CD) * δ := by
        intro σ hσ
        rw [Set.uIoc_of_le hs.2] at hσ
        exact hpt σ (Set.Ioc_subset_Icc_self hσ)
      have hC : 0 ≤ (LD * Kc + CD) * δ := by
        have h1 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
        nlinarith [h1, hCDpos.le, hδnn]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hb) ?_
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 19 / 20 - s)]
      have hbs : 19 / 20 - s ≤ 19 / 20 - 1 / 4 := by linarith [hs.1]
      have hK3 : 0 ≤ LD * Kc + CD := by
        have h1 : 0 ≤ LD * Kc := mul_nonneg hLDpos.le hKc
        linarith [h1, hCDpos.le]
      calc (LD * Kc + CD) * δ * (19 / 20 - s)
          ≤ (LD * Kc + CD) * δ * (19 / 20 - 1 / 4) :=
            mul_le_mul_of_nonneg_left hbs (mul_nonneg hK3 hδnn)
        _ = ((7 / 10) * (LD * Kc + CD)) * δ := by ring_nf
    -- term 4: the source
    have hterm4 : ‖XsCl n h s - XsCl n 0 s‖ ≤ CX * δ := hXscl h δ hh hδpos hδ100 hjet hsupp s hs
    -- assemble
    have hsplit : (- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
          (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
        - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
          (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)
        = (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s)))
          + (-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
          + (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
            + (XsCl n h s - XsCl n 0 s)) := by abel
    have h5 : ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖ ≤ (Cgs * Kc + Cgs) * δ := by
      rw [norm_neg]; exact hterm1
    have h6 : ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
        ≤ (MTh * Kc + CTh) * δ := by rw [norm_neg]; exact hterm2
    have h1 := norm_add_le (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
        + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
      (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
          (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) + (XsCl n h s - XsCl n 0 s))
    have h2 := norm_add_le (-(GsCl n h s (Z s) - GsCl n 0 s (baseState s)))
      (-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
    have h3 := norm_add_le ((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) (XsCl n h s - XsCl n 0 s)
    have h7 : ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖
        + ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
        + (‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
          + ‖XsCl n h s - XsCl n 0 s‖)
        ≤ ((Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((7 / 10) * (LD * Kc + CD)) + CX + 1) * δ := by
      nlinarith [h5, h6, hterm3, hterm4, hCgsnn, hMThnn, hCDpos.le, hLDpos.le, hCX, hCThpos.le,
        hKc, hδnn]
    calc ‖(- GsCl n h s (Z s) - WinData.Tcl n h s s (Z s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) + XsCl n h s)
          - (- GsCl n 0 s (baseState s) - WinData.Tcl n 0 s s (baseState s) +
            (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)) + XsCl n 0 s)‖
        = ‖(-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
            + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s)))
            + (((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
                (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
              + (XsCl n h s - XsCl n 0 s))‖ := by rw [hsplit]
      _ ≤ ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))
            + -(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
          + ‖((∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ)))
            + (XsCl n h s - XsCl n 0 s)‖ := h1
      _ ≤ ‖-(GsCl n h s (Z s) - GsCl n 0 s (baseState s))‖
            + ‖-(WinData.Tcl n h s s (Z s) - WinData.Tcl n 0 s s (baseState s))‖
          + (‖(∫ σ in s..(19 / 20 : ℝ), TsCl n h s σ (Z σ)) -
              (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))‖
            + ‖XsCl n h s - XsCl n 0 s‖) := by linarith [h2, h3]
      _ ≤ ((Cgs * Kc + Cgs) + (MTh * Kc + CTh) + ((7 / 10) * (LD * Kc + CD)) + CX + 1) * δ := h7

end

end Work.OddCurveB.Step2
