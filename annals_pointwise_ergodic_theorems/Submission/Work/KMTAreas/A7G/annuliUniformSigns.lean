import Mathlib
import Submission.Work.KMTAreas.A7Lpd.incrementVar
import Submission.Work.KMTAreas.A7Hi.FiberOpUniformLp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7G

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

theorem annuliUniformSigns (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
        ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hq1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  set q : ℝ := p.toReal with hqdef
  have hq1' : 1 < q := by rw [hqdef]; exact hq1
  let rr : ℕ := max 2 ⌈max q (q / (q - 1)) / 2⌉₊
  have hrr2 : 2 ≤ rr := le_max_left 2 _
  have hE1 : 1 < 2 * (rr : ℝ) := by
    have h2 : (2 : ℝ) ≤ (rr : ℝ) := by exact_mod_cast hrr2
    linarith
  obtain ⟨M, hMpos, hM⟩ :=
    Work.KMTAreas.A7Lpd.isLqMultiplierBound_annulus (2 * (rr : ℝ)) hE1
  obtain ⟨C1, hC1pos, Cρ1, hCρ1pos, hbump⟩ :=
    Work.KMTAreas.A7Hi.iwLqBound_narrow_bump ρ hρ hρ1 q hq1'
  have hCMpos : (0 : ℝ) < C1 * (M : ℝ) := mul_pos hC1pos (by exact_mod_cast hMpos)
  refine ⟨max Cρ1 2, lt_max_of_lt_right (by norm_num), C1 * (M : ℝ) + 1, by positivity, ?_⟩
  intro l m₀ hgood U ω f
  rw [← hpq]
  by_cases hfin : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count = ⊤
  · have hne : ENNReal.ofReal (C1 * (M : ℝ) + 1) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    rw [hfin, ENNReal.mul_top hne]
    exact le_top
  · have hflt : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr hfin
    obtain ⟨B, hB⟩ := Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal q)
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1'.le) f hflt
    have hnarrow : ∀ n ξ, (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
      intro n ξ hξ
      simp only [Work.KMTAreas.A7Lpd.annSch_coe] at hξ
      have hcases : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ ≠ 0 ∨
          Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hξ (by rw [hcon.1, hcon.2]; ring)
      rcases hcases with h1 | h2
      · exact Work.Analysis.IonescuWainger.realArc_mono (by omega)
          (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ h1)
      · exact Work.Analysis.IonescuWainger.realArc_mono (by omega)
          (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ h2)
    have hm02 : 2 ≤ m₀ := by
      have h := hgood
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at h
      have h' : -(m₀ : ℝ) ≤ -max Cρ1 2 * (2 : ℝ) ^ (ρ * (l : ℝ)) := by simpa using h
      have h2 : (2 : ℝ) ≤ max Cρ1 2 := le_max_right Cρ1 2
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hle : -(m₀ : ℝ) ≤ -2 := by nlinarith [h', h2, hpos, hge1]
      have h2' : (2 : ℝ) ≤ (m₀ : ℝ) := by linarith
      exact_mod_cast h2'
    have hk : (2 : ℝ) ^ (-(m₀ : ℤ)) < 1 / 2 := by
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ m₀ := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ m₀ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm02
      rw [zpow_neg, zpow_natCast, inv_eq_one_div]
      have hle : 1 / (2 : ℝ) ^ m₀ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
      linarith
    set Sfin : ℝ → ℂ := fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) ξ with hSfindef
    have hSnarrow : ∀ ξ : ℝ, Sfin ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
      intro ξ hξ
      by_contra hcon
      have hzero : ∀ n : ℕ, (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) ξ = 0 := fun n => by
        by_contra hn
        exact hcon (hnarrow n ξ hn)
      apply hξ
      rw [hSfindef]
      exact Finset.sum_eq_zero (fun n _ => by rw [hzero n, mul_zero])
    have hScd : ContDiff ℝ (⊤ : ℕ∞) Sfin := by
      rw [hSfindef]
      exact ContDiff.sum (s := U)
        (f := fun n ξ => (if ω n then (1 : ℂ) else -1) *
          (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) ξ)
        (fun n _ => contDiff_const.mul ((Work.KMTAreas.A7Lpd.annSch m₀ n).smooth ⊤))
    have hScs : HasCompactSupport Sfin :=
      HasCompactSupport.of_support_subset_isCompact
        (K := Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ))) isCompact_Icc
        (fun ξ hξ => hSnarrow ξ hξ)
    let Ssch : SchwartzMap ℝ ℂ := hScs.toSchwartzMap hScd
    have hScoe : (Ssch : ℝ → ℂ) = Sfin := by
      funext x
      exact HasCompactSupport.toSchwartzMap_toFun hScs hScd x
    have hnarrowS : ∀ x : ℝ, (Ssch : ℝ → ℂ) x ≠ 0 →
        x ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
      intro x hx
      exact hSnarrow x (by rwa [hScoe] at hx)
    have hmult1 : Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (rr : ℝ)))
        (Ssch : ℝ → ℂ) M := by
      have h := hM m₀ U ω
      rw [hScoe, hSfindef]
      exact h
    have hmult2 : Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (rr : ℝ)))
        (fun x : ℝ => star ((Ssch : ℝ → ℂ) x)) M :=
      Work.KMTAreas.A7.IsLqMultiplierBound_star hmult1
    have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ1 l (-(m₀ : ℤ)) :=
      Work.KMTAreas.A7Lpd.goodMajorArcs_mono (le_max_left Cρ1 2) hgood
    have hIW : Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) (ENNReal.ofReal q)
        (Real.toNNReal (C1 * (M : ℝ))) :=
      hbump l (-(m₀ : ℤ)) Ssch M hgood' hk hnarrowS hmult1 hmult2
    have hbound := Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) Ssch hq1'
      (Real.toNNReal_pos.mpr hCMpos) hIW
    have hTle : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) f
        = fun x : ℤ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x :=
      fun n => Work.KMTAreas.A7Lpd.Tle_annSch_eq ρ l m₀ n f hB
    have hfun : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        = (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) f x) := by
      funext x
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hTle n]
    have hlin := Work.KMTAreas.A7.Tle_finsetSum_of_bounded ρ l (-(m₀ : ℤ)) hk
      (fun n => Work.KMTAreas.A7Lpd.annSch m₀ n) hnarrow U ω hB
    calc MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
          (ENNReal.ofReal q) MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7Lpd.annSch m₀ n : ℝ → ℂ) f x)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by rw [hfun]
      _ = MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l Sfin f)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by rw [hlin, hSfindef]
      _ = MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) f)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by rw [hScoe]; rfl
      _ ≤ ENNReal.ofReal ((Real.toNNReal (C1 * (M : ℝ)) : NNReal) : ℝ) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count :=
          hbound f
      _ ≤ ENNReal.ofReal (C1 * (M : ℝ) + 1) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          rw [Real.coe_toNNReal _ hCMpos.le]
          exact ENNReal.ofReal_le_ofReal (by linarith)

end

end Work.KMTAreas.A7G
