
/-
# The single-chain block square function, unconditionally
-/
import Mathlib
import Submission.Work.KMTAreas.A7Lpd.incrementVar
import Submission.Work.KMTAreas.A7Lpd.chainBlockVar

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Lpd

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-- **The uniform-in-signs bound for the annuli of the low-pass family**, at the real exponent
`q`.  (Same statement as `Work.KMTAreas.A7G.annuliUniformSigns`, re-proved here so that the
single-chain bound below is self-contained.) -/
theorem uniformSignsAnnuliOfReal (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (q : ℝ) (hq : 1 < q) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
        ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
          (ENNReal.ofReal q) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  let rr : ℕ := max 2 ⌈max q (q / (q - 1)) / 2⌉₊
  have hrr2 : 2 ≤ rr := le_max_left 2 _
  have hE1 : 1 < 2 * (rr : ℝ) := by
    have h2 : (2 : ℝ) ≤ (rr : ℝ) := by exact_mod_cast hrr2
    linarith
  obtain ⟨M, hMpos, hM⟩ := isLqMultiplierBound_annulus (2 * (rr : ℝ)) hE1
  obtain ⟨C1, hC1pos, Cρ1, hCρ1pos, hbump⟩ :=
    Work.KMTAreas.A7Hi.iwLqBound_narrow_bump ρ hρ hρ1 q hq
  have hCMpos : (0 : ℝ) < C1 * (M : ℝ) := mul_pos hC1pos (by exact_mod_cast hMpos)
  refine ⟨max Cρ1 2, lt_max_of_lt_right (by norm_num), C1 * (M : ℝ) + 1, by positivity, ?_⟩
  intro l m₀ hgood U ω f
  by_cases hfin : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count = ⊤
  · have hne : ENNReal.ofReal (C1 * (M : ℝ) + 1) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    rw [hfin, ENNReal.mul_top hne]
    exact le_top
  · have hflt : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr hfin
    obtain ⟨B, hB⟩ := Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal q)
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le) f hflt
    have hnarrow : ∀ n ξ, (annSch m₀ n : ℝ → ℂ) ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
      intro n ξ hξ
      simp only [annSch_coe] at hξ
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
        (annSch m₀ n : ℝ → ℂ) ξ with hSfindef
    have hSnarrow : ∀ ξ : ℝ, Sfin ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
      intro ξ hξ
      by_contra hcon
      have hzero : ∀ n : ℕ, (annSch m₀ n : ℝ → ℂ) ξ = 0 := fun n => by
        by_contra hn
        exact hcon (hnarrow n ξ hn)
      apply hξ
      rw [hSfindef]
      exact Finset.sum_eq_zero (fun n _ => by rw [hzero n, mul_zero])
    have hScd : ContDiff ℝ (⊤ : ℕ∞) Sfin := by
      rw [hSfindef]
      exact ContDiff.sum (s := U)
        (f := fun n ξ => (if ω n then (1 : ℂ) else -1) * (annSch m₀ n : ℝ → ℂ) ξ)
        (fun n _ => contDiff_const.mul ((annSch m₀ n).smooth ⊤))
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
    have hmult1 : IsLqMultiplierBound (ENNReal.ofReal (2 * (rr : ℝ)))
        (Ssch : ℝ → ℂ) M := by
      have h := hM m₀ U ω
      rw [hScoe, hSfindef]
      exact h
    have hmult2 : IsLqMultiplierBound (ENNReal.ofReal (2 * (rr : ℝ)))
        (fun x : ℝ => star ((Ssch : ℝ → ℂ) x)) M :=
      Work.KMTAreas.A7.IsLqMultiplierBound_star hmult1
    have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ1 l (-(m₀ : ℤ)) :=
      goodMajorArcs_mono (le_max_left Cρ1 2) hgood
    have hIW : IWLqBound (iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) (ENNReal.ofReal q)
        (Real.toNNReal (C1 * (M : ℝ))) :=
      hbump l (-(m₀ : ℤ)) Ssch M hgood' hk hnarrowS hmult1 hmult2
    have hbound := Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
      (iwArithFreqs ρ l) Ssch hq (Real.toNNReal_pos.mpr hCMpos) hIW
    have hTle : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ l (annSch m₀ n : ℝ → ℂ) f
        = fun x : ℤ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x :=
      fun n => Tle_annSch_eq ρ l m₀ n f hB
    have hfun : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        = (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l (annSch m₀ n : ℝ → ℂ) f x) := by
      funext x
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hTle n]
    have hlin := Work.KMTAreas.A7.Tle_finsetSum_of_bounded ρ l (-(m₀ : ℤ)) hk
      (fun n => annSch m₀ n) hnarrow U ω hB
    calc MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
          (ENNReal.ofReal q) MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l (annSch m₀ n : ℝ → ℂ) f x)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by rw [hfun]
      _ = MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l Sfin f)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by
        rw [hlin]
      _ = MeasureTheory.eLpNorm (iwConv (iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) f)
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by
        change MeasureTheory.eLpNorm (iwConv (iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize Sfin) f)
            (ENNReal.ofReal q) MeasureTheory.Measure.count
          = MeasureTheory.eLpNorm (iwConv (iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Ssch : ℝ → ℂ)) f)
            (ENNReal.ofReal q) MeasureTheory.Measure.count
        rw [hScoe]
      _ ≤ ENNReal.ofReal ((Real.toNNReal (C1 * (M : ℝ)) : NNReal) : ℝ) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count :=
          hbound f
      _ ≤ ENNReal.ofReal (C1 * (M : ℝ) + 1) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count := by
          refine mul_le_mul_of_nonneg_right ?_ bot_le
          rw [Real.coe_toNNReal _ hCMpos.le]
          exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The unconditional single-chain block square function bound.** -/
theorem singleChain_blockSqSum_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
        MeasureTheory.eLpNorm (fun x : ℤ => (∑' i : ℕ, if i < J then
            ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0)
            ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  obtain ⟨Cρ, hCρ, C, hC, hAnn⟩ := uniformSignsAnnuliOfReal ρ hρ hρ1 p.toReal hp1
  obtain ⟨C', hC', hmain⟩ :=
    singleChain_blockSqSum_le_of_uniformSigns ρ p hp hptop Cρ C hC (fun l m₀ hg => by
      have h := hAnn l m₀ hg
      rwa [hpq] at h)
  refine ⟨Cρ, hCρ, C', hC', ?_⟩
  intro l m₀ hg f J N hN
  exact hmain l m₀ hg f J N hN

end

end Work.KMTAreas.A7Lpd
