/-
# `Work.FIArea5.S16Hecke.mellin_cut_facts`

The analytic facts about the two cut integrals of the theta series that feed into the
construction of Hecke's functional equation.

For the truncated theta series

* `thetaCut d chi m u = if thetaC d < u then thetaHol chi m u else 0` and
* `thetaCutStar d chi m v = if thetaC d < v then conj (thetaHol chi m v) else 0`

(vanishing below `thetaC d > 0`, exponential decay at `∞`, and locally integrable on `(0,∞)`),
the Mellin transform converges everywhere, and the "Hecke" functions

* `heckeA d chi m t = ∫_c^∞ θ(u) u^{t-1} du  = mellin (thetaCut d chi m) t`,
* `heckeE d chi m t = ∫_c^∞ conj θ(v) v^{m-t} dv = mellin (thetaCutStar d chi m) (m+1-t)`

are entire.  All of this follows from the general cut-function lemma `mellin_cut_props`
applied to the two truncations.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.mellin_cut_props

namespace Work.FIArea5.S16Hecke

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- `thetaCut` is dominated by `thetaHol` pointwise. -/
lemma thetaCut_norm_le_thetaHol (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    ‖thetaCut d chi m u‖ ≤ ‖thetaHol chi m u‖ := by
  rw [thetaCut]; split_ifs <;> simp

/-- `thetaCutStar` is dominated by `thetaHol` pointwise (conjugation preserves the norm). -/
lemma thetaCutStar_norm_le_thetaHol (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    ‖thetaCutStar d chi m u‖ ≤ ‖thetaHol chi m u‖ := by
  rw [thetaCutStar]; split_ifs <;> simp

/-- A function vanishing on `(-∞, 0]` which is a.e. strongly measurable on `(0, ∞)` is a.e. strongly
measurable for the full volume: it is the indicator of `(0, ∞)` times itself. -/
lemma aestronglyMeasurable_of_eq_zero_of_nonpos {g : ℝ → ℂ}
    (h : ∀ u : ℝ, u ≤ 0 → g u = 0) (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioi 0))) :
    AEStronglyMeasurable g volume := by
  have hpt : ∀ u : ℝ, Set.indicator (Set.Ioi (0 : ℝ)) g u = g u := by
    intro u
    rcases lt_or_ge (0 : ℝ) u with hu | hu
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu)]
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; exact not_lt.mpr hu), h u hu]
  have h1 : AEStronglyMeasurable (Set.indicator (Set.Ioi (0 : ℝ)) g) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr hg
  exact h1.congr (Filter.Eventually.of_forall hpt)

theorem mellin_cut_facts (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hmeas : AEMeasurable (thetaHol chi m) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hli : MeasureTheory.LocallyIntegrableOn (thetaHol chi m) (Set.Ioi 0))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ‖thetaHol chi m u‖ ≤ C * Real.exp (-Real.pi * u)) :
    (∀ t : ℂ, MellinConvergent (thetaCut d chi m) t) ∧
      (∀ t : ℂ, MellinConvergent (thetaCutStar d chi m) t) ∧
      AnalyticOn ℂ (heckeA d chi m) Set.univ ∧ AnalyticOn ℂ (heckeE d chi m) Set.univ := by
  have hc : 0 < thetaC d := thetaC_pos hd
  obtain ⟨C, u₀, hu₀, hC⟩ := hdec
  -- ## Measurability of the two truncations
  have hmeasCut : AEMeasurable (thetaCut d chi m) (volume.restrict (Set.Ioi 0)) :=
    hmeas.indicator measurableSet_Ioi
  have hmeasStar : AEMeasurable (thetaCutStar d chi m) (volume.restrict (Set.Ioi 0)) :=
    (Measurable.comp_aemeasurable (f := thetaHol chi m) (g := star)
      continuous_star.measurable hmeas).indicator measurableSet_Ioi
  -- ## Global a.e. strong measurability (both truncations vanish on `(-∞,0]`)
  have hglobCut : AEStronglyMeasurable (thetaCut d chi m) volume :=
    aestronglyMeasurable_of_eq_zero_of_nonpos
      (fun u hu => by rw [thetaCut, if_neg (not_lt.mpr (le_trans hu hc.le))])
      hmeasCut.aestronglyMeasurable
  have hglobStar : AEStronglyMeasurable (thetaCutStar d chi m) volume :=
    aestronglyMeasurable_of_eq_zero_of_nonpos
      (fun u hu => by rw [thetaCutStar, if_neg (not_lt.mpr (le_trans hu hc.le))])
      hmeasStar.aestronglyMeasurable
  -- ## Local integrability, by domination by `thetaHol`
  have hliCut : LocallyIntegrableOn (thetaCut d chi m) (Set.Ioi 0) :=
    hli.mono hglobCut (Filter.Eventually.of_forall (fun u => thetaCut_norm_le_thetaHol d chi m u))
  have hliStar : LocallyIntegrableOn (thetaCutStar d chi m) (Set.Ioi 0) :=
    hli.mono hglobStar (Filter.Eventually.of_forall (fun u => thetaCutStar_norm_le_thetaHol d chi m u))
  -- ## Vanishing below `thetaC d`
  have h0Cut : ∀ u : ℝ, u ≤ thetaC d → thetaCut d chi m u = 0 :=
    fun u hu => by rw [thetaCut, if_neg (not_lt.mpr hu)]
  have h0Star : ∀ u : ℝ, u ≤ thetaC d → thetaCutStar d chi m u = 0 :=
    fun u hu => by rw [thetaCutStar, if_neg (not_lt.mpr hu)]
  -- ## Exponential decay
  have hdecCut : ∃ C u₀ : ℝ, 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u → ‖thetaCut d chi m u‖ ≤ C * Real.exp (-Real.pi * u) :=
    ⟨C, u₀, hu₀, fun u hu => le_trans (thetaCut_norm_le_thetaHol d chi m u) (hC u hu)⟩
  have hdecStar : ∃ C u₀ : ℝ, 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u → ‖thetaCutStar d chi m u‖ ≤ C * Real.exp (-Real.pi * u) :=
    ⟨C, u₀, hu₀, fun u hu => le_trans (thetaCutStar_norm_le_thetaHol d chi m u) (hC u hu)⟩
  -- ## Apply the general cut-function lemma to both truncations
  obtain ⟨hAc, hAa⟩ :=
    mellin_cut_props (thetaC d) hc (thetaCut d chi m) hmeasCut hliCut h0Cut hdecCut
  obtain ⟨hSc, hSa⟩ :=
    mellin_cut_props (thetaC d) hc (thetaCutStar d chi m) hmeasStar hliStar h0Star hdecStar
  refine ⟨hAc, hSc, ?_, ?_⟩
  · exact hAa
  · -- `heckeE t = mellin (thetaCutStar) (m + 1 - t)`, an affine reparametrisation
    have hE : AnalyticOn ℂ (fun t : ℂ => ((m : ℂ) + 1) - t) Set.univ :=
      (analyticOn_const (v := ((m : ℂ) + 1)) (s := (Set.univ : Set ℂ))).sub analyticOn_id
    exact hSa.comp hE (fun t _ => Set.mem_univ _)

end

end Work.FIArea5.S16Hecke
