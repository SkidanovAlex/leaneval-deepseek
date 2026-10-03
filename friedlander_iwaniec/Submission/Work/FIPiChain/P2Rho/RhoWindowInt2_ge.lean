import Mathlib
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.Work.FIChain.RhoWin2Box
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.chainWindowFacts
import Submission.Work.FIChain.zc_DpiC_range
import Submission.Work.FIChain.bprime_window_tail_le
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FITop.RCPrelude
import Submission.Work.FIChain.RhoWin2Moment
import Submission.Work.FIChain.RhoWin2Main
import Submission.Work.FIChain.RhoWin2TailInlined
import Submission.Work.FIChain.RhoWin2Integrable
import Submission.Work.FIPiChain.P2Rho.RhoWin2RangeCm

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain.P2Rho

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem RhoWindowInt2_ge (h : Work.FITop4.Prop41StatementPiBig) :
    ∃ B₂ : ℝ, 0 < B₂ ∧ ∀ B : ℝ, B₂ ≤ B → ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      Work.FIChain.RhoWindowInt2 Work.FIChain.atilc x Work.FIChain.wc
        (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
        (Work.FIChain.zc x B) (Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)) := by
  -- ## the fixed inputs: the `Π`-restricted box, the `τ⁶`-moment, the two integrated bounds
  obtain ⟨K₀, hK₀pos, B₀, hB₀pos, xBox, hBox⟩ :=
    Work.FIChain.RhoWin2Box h ((1 : ℝ) / 256) (by norm_num) (by norm_num)
  obtain ⟨C₆, hC₆pos, xMom, hMom⟩ := Work.FIChain.RhoWin2Moment
  obtain ⟨Kmain, hKmainpos, hMain⟩ := Work.FIChain.RhoWin2Main
  obtain ⟨Ktail, hKtailpos, hTail⟩ := Work.FIChain.RhoWin2TailInlined
  obtain ⟨xt, hxt⟩ := Filter.eventually_atTop.mp hTail
  -- ## the free constant `B`, and the ladder constant
  refine ⟨B₀ + 5, by linarith, ?_⟩
  intro B hB
  have hB4 : (4 : ℝ) ≤ B := by linarith
  have hB5 : B₀ + 5 ≤ B := hB
  obtain ⟨xcm, hxcm⟩ := RhoWin2RangeCm B B₀ hB4 hB5
  refine ⟨Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) + Ktail + 1,
    max (max xBox xMom) (max xt xcm) + 3, by positivity, ?_⟩
  intro x hx
  have hxBox : xBox ≤ x := by omega
  have hxMom : xMom ≤ x := by omega
  have hxt' : xt ≤ x := by omega
  have hxcm' : xcm ≤ x := by omega
  rw [Work.FIChain.RhoWindowInt2]
  -- ## the local vocabulary
  set Cm : ℝ := (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ)) with hCmdef
  set D : ℝ := (Work.FIChain.DpiC x : ℝ) with hDdef
  set Pz : ℕ := Work.FIChain.Pzc x with hPzdef
  set lo : ℝ := Work.FIChain.zc x B with hlodef
  set hi : ℝ := Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B) with hhidef
  -- ## the range facts (delegated)
  obtain ⟨hb_log, hb_zcpos, hb_Cm1, hb_CmLe, hb_bot, hb_top, hb_log1, hb_log2, hb_log3,
    hb_Dpi1, hb_Pz2, hb_Pzlo, hb_Pzhi⟩ := hxcm x hxcm'
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := hb_log
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hD1 : 1 ≤ D := hb_Dpi1
  have hCm1 : 1 ≤ Cm := hb_Cm1
  have hlo_pos : 0 < lo := hb_zcpos
  have hsc1 : 1 ≤ Work.FIChain.sc x B := by
    rw [Work.FIChain.sc]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlohi : lo ≤ hi := by
    have h2 : (1 : ℝ) * (1 * lo) ≤ Real.exp 1 * (Work.FIChain.sc x B * lo) :=
      mul_le_mul hexp1 (mul_le_mul_of_nonneg_right hsc1 hlo_pos.le)
        (by linarith) (le_of_lt (Real.exp_pos 1))
    calc lo = 1 * (1 * lo) := by ring
      _ ≤ Real.exp 1 * (Work.FIChain.sc x B * lo) := h2
      _ = hi := rfl
  -- ## the box input of `RhoWin2Main`
  have hA : ∀ u : ℝ, lo / D ≤ u → u ≤ hi → ∀ σ : ℝ, 1 ≤ σ → σ ≤ Cm →
      (∑ c ∈ Finset.Icc 1 x, |Work.FIChain.Xpg x Pz c σ u|)
        ≤ K₀ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
    intro u hu1 hu2 σ hσ1 hσ2
    have hu_lo : (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 256) + 1 < u := by
      refine lt_of_lt_of_le hb_bot ?_
      have h := hu1
      rw [hlodef, hDdef] at h
      exact h
    have hu_hi : u ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) :=
      le_trans hu2 hb_top
    have hzu : Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ)) ≤ u / 2 := by
      have h := hu1
      rw [hlodef, hDdef] at h
      calc Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ))
          = Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) / 2 := by ring
        _ ≤ u / 2 := by linarith
    have hσ : σ ≤ (u / 2) ^ (1 - (1 : ℝ) / 256) :=
      le_trans hσ2 (le_trans hb_CmLe (Real.rpow_le_rpow (by positivity) hzu (by norm_num)))
    exact hBox x hxBox Pz hb_Pz2 hb_Pzlo hb_Pzhi u σ hu_lo hu_hi hσ1 hσ
  have hmom : ∀ σ u : ℝ,
      (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Work.FIChain.Xpg x Pz c σ u|)
        ≤ C₆ * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) :=
    fun σ u => hMom x hxMom Pz σ u
  -- ## integrability of the `Wall`-integrand
  obtain ⟨hIm_s, hIt_s, hIm_t, hIt_t, hIW_t⟩ :=
    Work.FIChain.RhoWin2Integrable x Pz D lo hi Cm hlo_pos hlohi hCm1
  have hWall_s : ∀ t : ℝ, IntervalIntegrable (fun s : ℝ => Work.FIChain.Wall x Pz s t / s)
      volume 1 Cm := by
    intro t
    have hfun : (fun s : ℝ => Work.FIChain.Wall x Pz s t / s)
        = fun s : ℝ => Work.FIChain.Wmain x Pz D s t / s + Work.FIChain.Wtail x Pz D s t / s := by
      funext s
      rw [Work.FIChain.Wall_eq_Wmain_add_Wtail]
      ring
    rw [hfun]
    exact (hIm_s t).add (hIt_s t)
  -- ## the range hypotheses of `RhoWin2Main` / `RhoWin2TailInlined`
  have hlog1 : Real.log (hi / (lo / D)) ≤ 2 * Real.log (x : ℝ) := hb_log1
  have hlog2 : Real.log Cm ≤ 2 * Real.log (x : ℝ) := hb_log2
  have hlog3 : Real.log (hi / lo) ≤ 2 * Real.log (x : ℝ) := hb_log3
  have hMainX := hMain x Pz D lo hi Cm K₀ C₆ hlo_pos hlohi hCm1 hD1 hK₀pos.le hC₆pos.le
    hL1 hlog1 hlog2 hA hmom
  have hTailX := hxt x hxt' lo hi Cm hlo_pos hlohi hCm1 hlog3 hlog2
  have hTailX' : (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wtail x Pz D s t / s) / t)
      ≤ Ktail * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := hTailX
  -- ## the pointwise domination of the `ρ`-integrand
  have hF_nonneg : ∀ s t : ℝ, 1 ≤ s →
      0 ≤ (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m *
        |Work.FITop.XrhoC Work.FIChain.atilc x m s t (2 * t)|) / s := by
    intro s t hs1
    refine div_nonneg (Finset.sum_nonneg (fun m _ => ?_)) (by linarith)
    refine mul_nonneg ?_ (abs_nonneg _)
    rw [show Work.FIChain.wc m = ((m.divisors.card : ℝ)) ^ 2 from rfl]
    positivity
  -- ## the inner and outer integral comparisons
  have hinner : ∀ t : ℝ,
      (∫ s in (1 : ℝ)..Cm,
        (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m *
          |Work.FITop.XrhoC Work.FIChain.atilc x m s t (2 * t)|) / s)
        ≤ ∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s := by
    intro t
    rw [intervalIntegral.integral_of_le hCm1, intervalIntegral.integral_of_le hCm1]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun s hs => hF_nonneg s t (le_of_lt hs.1))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hCm1).mp (hWall_s t)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun s hs => div_le_div_of_nonneg_right
          (Work.FIChain.XrhoC_le_Wall x Pz s t) (by linarith [hs.1]))
  have houter : (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm,
        (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m *
          |Work.FITop.XrhoC Work.FIChain.atilc x m s t (2 * t)|) / s) / t)
      ≤ ∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s) / t := by
    rw [intervalIntegral.integral_of_le hlohi, intervalIntegral.integral_of_le hlohi]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      have ht0 : 0 < t := lt_of_lt_of_le hlo_pos (le_of_lt ht.1)
      refine div_nonneg ?_ ht0.le
      exact intervalIntegral.integral_nonneg_of_ae_restrict hCm1
        (ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => hF_nonneg s t hs.1))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlohi).mp hIW_t
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      have ht0 : 0 < t := lt_of_lt_of_le hlo_pos (le_of_lt ht.1)
      exact div_le_div_of_nonneg_right (hinner t) ht0.le
  -- ## the split `Wall = Wmain + Wtail` inside the double integral
  have hint_split : ∀ t : ℝ, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s)
      = (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wmain x Pz D s t / s)
        + (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wtail x Pz D s t / s) := by
    intro t
    have h1 : (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s)
        = ∫ s in (1 : ℝ)..Cm,
            (Work.FIChain.Wmain x Pz D s t / s + Work.FIChain.Wtail x Pz D s t / s) :=
      intervalIntegral.integral_congr (fun s _ => by
        rw [Work.FIChain.Wall_eq_Wmain_add_Wtail]; ring)
    rw [h1, intervalIntegral.integral_add (hIm_s t) (hIt_s t)]
  have hsplit : (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s) / t)
      = (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wmain x Pz D s t / s) / t)
        + (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wtail x Pz D s t / s) / t) := by
    have hpt : (fun t : ℝ => (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s) / t)
        = fun t : ℝ => (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wmain x Pz D s t / s) / t
            + (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wtail x Pz D s t / s) / t := by
      funext t
      rw [hint_split t]
      ring
    rw [hpt, intervalIntegral.integral_add hIm_t hIt_t]
  -- ## assembly
  have hstep1 : (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm,
        (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m *
          |Work.FITop.XrhoC Work.FIChain.atilc x m s t (2 * t)|) / s) / t)
      ≤ Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * Work.FIChain.AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(5 : ℤ))
        + Ktail * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
    calc (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm,
            (∑ m ∈ Finset.Icc 1 x, Work.FIChain.wc m *
              |Work.FITop.XrhoC Work.FIChain.atilc x m s t (2 * t)|) / s) / t)
        ≤ (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wall x Pz s t / s) / t) := houter
      _ = (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wmain x Pz D s t / s) / t)
            + (∫ t in lo..hi, (∫ s in (1 : ℝ)..Cm, Work.FIChain.Wtail x Pz D s t / s) / t) :=
          hsplit
      _ ≤ Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * Work.FIChain.AcountAtilC x
            * (Real.log (x : ℝ)) ^ (-(5 : ℤ))
          + Ktail * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) :=
          add_le_add hMainX hTailX'
  have hA0 : 0 ≤ Work.FIChain.AcountAtilC x := Work.FIChain.AcountAtilC_nonneg' x
  refine le_trans hstep1 ?_
  have hXnn : 0 ≤ Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg hKmainpos.le (Real.rpow_nonneg hK₀pos.le _))
      (Real.rpow_nonneg hC₆pos.le _)
  have hpq : (Real.log (x : ℝ)) ^ (-(5 : ℤ)) ≤ (Real.log (x : ℝ)) ^ (-(4 : ℤ)) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  have h1 : Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * Work.FIChain.AcountAtilC x
        * (Real.log (x : ℝ)) ^ (-(5 : ℤ))
      ≤ Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * Work.FIChain.AcountAtilC x
        * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) :=
    mul_le_mul_of_nonneg_left hpq (mul_nonneg hXnn hA0)
  have h2 : 0 ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) :=
    mul_nonneg hA0 (le_of_lt (zpow_pos hLpos _))
  rw [show (Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) + Ktail + 1)
        * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))
      = Kmain * K₀ ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * Work.FIChain.AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(4 : ℤ))
        + Ktail * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))
        + Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) by ring]
  linarith [h1, h2]

end

end Work.FIPiChain.P2Rho
