import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs
import Submission.Work.FIArea5.S16Hecke.mellin_cut_props
import Submission.Work.FIArea5.S16Hecke.mellin_cut_facts

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

noncomputable section

theorem levCutFacts (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ)
    (hmeas : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hli : MeasureTheory.LocallyIntegrableOn f (Set.Ioi (0 : ℝ)))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ‖f u‖ ≤ C * Real.exp (-Real.pi * u)) :
    (∀ t : ℂ, MellinConvergent (thetaCutHi B f) t) ∧
      (∀ t : ℂ, MellinConvergent (thetaCutHiStar B f) t) ∧
      AnalyticOn ℂ (thetaA B f) Set.univ ∧ AnalyticOn ℂ (thetaE B f m) Set.univ := by
  have hc : 0 < thetaCutPt B := thetaCutPt_pos hB
  obtain ⟨C, u₀, hu₀, hC⟩ := hdec
  -- ## Measurability of the two truncations
  have hmeasCut : AEMeasurable (thetaCutHi B f) (volume.restrict (Set.Ioi 0)) :=
    hmeas.indicator measurableSet_Ioi
  have hmeasStar : AEMeasurable (thetaCutHiStar B f) (volume.restrict (Set.Ioi 0)) :=
    (Measurable.comp_aemeasurable (f := f) (g := star)
      continuous_star.measurable hmeas).indicator measurableSet_Ioi
  -- ## Global a.e. strong measurability (both truncations vanish on `(-∞,0]`)
  have hglobCut : AEStronglyMeasurable (thetaCutHi B f) volume :=
    Work.FIArea5.S16Hecke.aestronglyMeasurable_of_eq_zero_of_nonpos
      (fun u hu => by rw [thetaCutHi, if_neg (not_lt.mpr (le_trans hu hc.le))])
      hmeasCut.aestronglyMeasurable
  have hglobStar : AEStronglyMeasurable (thetaCutHiStar B f) volume :=
    Work.FIArea5.S16Hecke.aestronglyMeasurable_of_eq_zero_of_nonpos
      (fun u hu => by rw [thetaCutHiStar, if_neg (not_lt.mpr (le_trans hu hc.le))])
      hmeasStar.aestronglyMeasurable
  -- ## Local integrability, by domination by `f`
  have hliCut : LocallyIntegrableOn (thetaCutHi B f) (Set.Ioi 0) :=
    hli.mono hglobCut (Filter.Eventually.of_forall (fun u => thetaCutHi_norm_le B f u))
  have hliStar : LocallyIntegrableOn (thetaCutHiStar B f) (Set.Ioi 0) :=
    hli.mono hglobStar (Filter.Eventually.of_forall (fun u => thetaCutHiStar_norm_le B f u))
  -- ## Vanishing below `thetaCutPt B`
  have h0Cut : ∀ u : ℝ, u ≤ thetaCutPt B → thetaCutHi B f u = 0 :=
    fun u hu => by rw [thetaCutHi, if_neg (not_lt.mpr hu)]
  have h0Star : ∀ u : ℝ, u ≤ thetaCutPt B → thetaCutHiStar B f u = 0 :=
    fun u hu => by rw [thetaCutHiStar, if_neg (not_lt.mpr hu)]
  -- ## Exponential decay
  have hdecCut : ∃ C u₀ : ℝ, 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u → ‖thetaCutHi B f u‖ ≤ C * Real.exp (-Real.pi * u) :=
    ⟨C, u₀, hu₀, fun u hu => le_trans (thetaCutHi_norm_le B f u) (hC u hu)⟩
  have hdecStar : ∃ C u₀ : ℝ, 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u → ‖thetaCutHiStar B f u‖ ≤ C * Real.exp (-Real.pi * u) :=
    ⟨C, u₀, hu₀, fun u hu => le_trans (thetaCutHiStar_norm_le B f u) (hC u hu)⟩
  -- ## Apply the general cut-function lemma to both truncations
  obtain ⟨hAc, hAa⟩ :=
    Work.FIArea5.S16Hecke.mellin_cut_props (thetaCutPt B) hc (thetaCutHi B f) hmeasCut hliCut h0Cut hdecCut
  obtain ⟨hSc, hSa⟩ :=
    Work.FIArea5.S16Hecke.mellin_cut_props (thetaCutPt B) hc (thetaCutHiStar B f) hmeasStar hliStar h0Star hdecStar
  refine ⟨hAc, hSc, ?_, ?_⟩
  · exact hAa
  · exact analyticOn_thetaE B f m hSa

end

end Work.FIArea6Hecke.R
