/-
# The narrow spike bound with the bounded-bump interface

This is `Work.KMTPlan.A6.spikeNarrowL2` (in the namespace `Work.KMTPlan.A6.Linf`) with the
single-scale estimate replaced by its `Linf` form: the abstract bump hypothesis `hSS` carries the
two extra hypotheses
`MemLp (periodize φ) ⊤ circleMeasure`, `MemLp (periodize ψ) ⊤ circleMeasure`, and the theorem
receives those for its own two bumps `φ, ψ` as the hypotheses `hMlpφ`, `hMlpψ` (produced by the
callers from measurability + the narrow supports `hφarc`/`hψarc` + the pointwise bounds
`hφb`/`hψb` via `Work.KMTPlan.A6.Linf.memLp_periodize_of_arc`).

The three auxiliary declarations used by the proof (`supportedInArc_mono_scale`,
`eLpNorm_ofReal_norm_eq`, `Tm_eq_zero_of_not_integrable`) are taken from the original module.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.spikeNarrowL2
import Submission.Work.KMTPlan.A6.LinfDefs

namespace Work.KMTPlan.A6.Linf

open MeasureTheory
open scoped ENNReal
open Work.Analysis.IonescuWainger

theorem spikeNarrowL2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (hSS : ∀ (m₁ m₂ u : ℕ) (φ ψ : ℝ → ℂ) (f' g' : ℤ → ℂ),
      (max m₁ m₂ : ℝ) ≤ (u : ℝ) →
      (2 : ℝ) ^ (ρ * (max m₁ m₂ : ℝ)) ≤ (u : ℝ) →
      MeasureTheory.MemLp f' 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g' 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
        Work.Analysis.IonescuWainger.circleMeasure →
      MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
        Work.Analysis.IonescuWainger.circleMeasure →
      (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
      (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P m₁ m₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ m₁ φ f') (Work.KMTAreas.A7.Tm ρ m₂ ψ g') x)
        1 MeasureTheory.Measure.count
      ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (m₁ : ℝ) (m₂ : ℝ)))))
          * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₁ φ f') 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₂ ψ g') 2 MeasureTheory.Measure.count)
    (l₁ l₂ u : ℕ) (hu : 1 ≤ u) (hmax1 : (max l₁ l₂ : ℝ) ≤ (u : ℝ))
    (hmax2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ))
    {φ ψ : ℝ → ℂ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hφb : ∀ ξ : ℝ, ‖φ ξ‖ ≤ Cb)
    (hφarc : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
    (hψb : ∀ ξ : ℝ, ‖ψ ξ‖ ≤ Cb)
    (hψarc : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
    (hMlpφ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (hMlpψ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (hNA₁ : Work.Analysis.IonescuWainger.NonAliasing (-(3 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : Work.Analysis.IonescuWainger.NonAliasing (-(3 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (f g : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x‖)
        1 MeasureTheory.Measure.count
      ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * (ENNReal.ofReal Cb * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
          * (ENNReal.ofReal Cb * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
  -- arithmetic: the two arc scales are `≤ -3`
  have h2φ : (2 : ℝ) ^ (-(3 * (u : ℤ)) + 1) < 1 := by
    have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
    have hk : ((-(3 * (u : ℤ)) + 1 : ℤ)) ≤ -2 := by
      have h3 : (3 : ℤ) ≤ 3 * (u : ℤ) := by linarith
      linarith
    calc (2 : ℝ) ^ (-(3 * (u : ℤ)) + 1) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) hk
      _ = 1 / 4 := by norm_num
      _ < 1 := by norm_num
  have h2ψ : (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)) + 1) < 1 := by
    have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
    have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
      have : 1 ≤ P.natDegree := by omega
      exact_mod_cast this
    have hk : ((-(3 * (P.natDegree : ℤ) * (u : ℤ)) + 1 : ℤ)) ≤ -2 := by
      have h3 : (3 : ℤ) ≤ 3 * (P.natDegree : ℤ) * (u : ℤ) := by nlinarith
      linarith
    calc (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)) + 1) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) hk
      _ = 1 / 4 := by norm_num
      _ < 1 := by norm_num
  -- the two periodisations are bounded by `Cb`
  have hperφ : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize φ ξ‖ ≤ Cb :=
    Work.Analysis.IWMultiplier.periodize_norm_le (k := -(3 * (u : ℤ))) h2φ
      (fun x hx => by
        rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
        exact ⟨neg_le_of_abs_le (hφarc x hx), le_of_abs_le (hφarc x hx)⟩) hφb
  have hperψ : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize ψ ξ‖ ≤ Cb :=
    Work.Analysis.IWMultiplier.periodize_norm_le (k := -(3 * (P.natDegree : ℤ) * (u : ℤ))) h2ψ
      (fun x hx => by
        rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
        exact ⟨neg_le_of_abs_le (hψarc x hx), le_of_abs_le (hψarc x hx)⟩) hψb
  -- the two periodisations are supported in the non-aliasing arc `ℝ_{≤-3u}`
  have hSIAφ : Work.Analysis.IonescuWainger.SupportedInArc (-(3 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.periodize φ) :=
    supportedInArc_periodize_of_support u hu φ hφarc
  have hSIAψ : Work.Analysis.IonescuWainger.SupportedInArc (-(3 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.periodize ψ) := by
    have huZ : (0 : ℤ) ≤ (u : ℤ) := by exact_mod_cast Nat.zero_le u
    have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
      have : 1 ≤ P.natDegree := by omega
      exact_mod_cast this
    have hkk : (-(3 * (P.natDegree : ℤ) * (u : ℤ))) ≤ (-(3 * (u : ℤ))) := by
      have h3 : 3 * (u : ℤ) ≤ 3 * (P.natDegree : ℤ) * (u : ℤ) := by nlinarith
      linarith
    exact supportedInArc_mono_scale hkk
      (supportedInArc_periodize_of_arc (k := -(3 * (P.natDegree : ℤ) * (u : ℤ)))
        (fun x hx => by
          rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
          exact ⟨neg_le_of_abs_le (hψarc x hx), le_of_abs_le (hψarc x hx)⟩))
  -- the narrow pointwise bounds on the two IW symbols
  have hsymφ : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₁)
        (Work.Analysis.IonescuWainger.periodize φ) ξ‖ ≤ Cb :=
    fun ξ => iwSymbolSet_narrow_bound ρ l₁ (-(3 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.periodize φ) Cb hCb hperφ hSIAφ hNA₁ ξ
  have hsymψ : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
        (Work.Analysis.IonescuWainger.periodize ψ) ξ‖ ≤ Cb :=
    fun ξ => iwSymbolSet_narrow_bound ρ l₂ (-(3 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.periodize ψ) Cb hCb hperψ hSIAψ hNA₂ ξ
  -- the single-scale estimate
  have hssu := hSS l₁ l₂ u φ ψ f g hmax1 hmax2 hf hg hMlpφ hMlpψ hφarc hψarc
  by_cases hI₁ : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.KMTAreas.A7.diffFreqs ρ l₁) (Work.Analysis.IonescuWainger.periodize φ))
      Work.Analysis.IonescuWainger.circleMeasure
  · by_cases hI₂ : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.KMTAreas.A7.diffFreqs ρ l₂) (Work.Analysis.IonescuWainger.periodize ψ))
        Work.Analysis.IonescuWainger.circleMeasure
    · have hMemLp₁ : MemLp (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.KMTAreas.A7.diffFreqs ρ l₁) (Work.Analysis.IonescuWainger.periodize φ))
          ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
        MemLp.of_bound hI₁.aestronglyMeasurable Cb (Filter.Eventually.of_forall hsymφ)
      have hMemLp₂ : MemLp (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.KMTAreas.A7.diffFreqs ρ l₂) (Work.Analysis.IonescuWainger.periodize ψ))
          ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
        MemLp.of_bound hI₂.aestronglyMeasurable Cb (Filter.Eventually.of_forall hsymψ)
      have hL2φ : MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f)
          2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Cb * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs ρ l₁)
          (Work.Analysis.IonescuWainger.periodize φ) Cb hCb hsymφ hMemLp₁ f hf
      have hL2ψ : MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g)
          2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Cb * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
        eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs ρ l₂)
          (Work.Analysis.IonescuWainger.periodize ψ) Cb hCb hsymψ hMemLp₂ g hg
      rw [eLpNorm_ofReal_norm_eq]
      exact hssu.trans (mul_le_mul' (mul_le_mul' le_rfl hL2φ) hL2ψ)
    · have hz₂ : Work.KMTAreas.A7.Tm ρ l₂ ψ g = 0 :=
        Tm_eq_zero_of_not_integrable (ρ := ρ) (l := l₂) (θ := ψ) (f := g) hI₂
      have hzero : (fun x : ℤ => ENNReal.ofReal ‖Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
            (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
            (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x‖) = 0 := by
        funext x
        simp only [Work.KMTPlan.A6.BtwistEx, hz₂, Pi.zero_apply, mul_zero, tsum_zero,
          norm_zero, ENNReal.ofReal_zero]
      rw [hzero]
      simp
  · have hz₁ : Work.KMTAreas.A7.Tm ρ l₁ φ f = 0 :=
      Tm_eq_zero_of_not_integrable (ρ := ρ) (l := l₁) (θ := φ) (f := f) hI₁
    have hzero : (fun x : ℤ => ENNReal.ofReal ‖Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x‖) = 0 := by
      funext x
      simp only [Work.KMTPlan.A6.BtwistEx, hz₁, Pi.zero_apply, zero_mul, mul_zero, tsum_zero,
        norm_zero, ENNReal.ofReal_zero]
    rw [hzero]
    simp

end Work.KMTPlan.A6.Linf
