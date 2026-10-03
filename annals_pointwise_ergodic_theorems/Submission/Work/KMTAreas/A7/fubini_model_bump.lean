import Mathlib
import Submission.Work.A7.ModelApproxCore_cw_fubini
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs

namespace Work.KMTAreas.A7

open MeasureTheory intervalIntegral

theorem fubini_model_bump (P : Polynomial ℤ) (N k₁ k₂ u : ℕ) (j₁ j₂ : ℤ) :
    ∫ t in (1 / 2 : ℝ)..1,
        Work.KMTAreas.A7.cw (fun ξ => Work.KMTAreas.A7.mStarF u ξ
            * Work.KMTAreas.A7.varphiNt N k₁ t ξ) j₁
          * Work.KMTAreas.A7.cw (fun ξ => Work.KMTAreas.A7.mStargF P.natDegree u ξ
            * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ) j₂
      = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
          Work.KMTAreas.A7.mStarF u θ₁ * Work.KMTAreas.A7.mStargF P.natDegree u θ₂
            * Work.KMTAreas.A7.varphiN N k₁ θ₁ * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
            * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
            * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)) := by
  obtain ⟨hAi, hAm⟩ := Work.A7.varphiN_integrable_measurable N k₁
  obtain ⟨hBi, hBm⟩ := Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂
  have hM1m : Measurable (mStarF u) :=
    (contDiff_etaCut (-(2 * (u : ℤ)))).continuous.measurable
  have hM1b : ∀ ξ : ℝ, ‖mStarF u ξ‖ ≤ 1 := fun ξ => norm_etaCut_le_one (-(2 * (u : ℤ))) ξ
  have hM2m : Measurable (mStargF P.natDegree u) :=
    (contDiff_etaCut (-((P.natDegree : ℤ) * 2 * (u : ℤ)))).continuous.measurable
  have hM2b : ∀ ξ : ℝ, ‖mStargF P.natDegree u ξ‖ ≤ 1 :=
    fun ξ => norm_etaCut_le_one (-((P.natDegree : ℤ) * 2 * (u : ℤ))) ξ
  have hai : Integrable (fun ξ => mStarF u ξ * varphiN N k₁ ξ) :=
    hAi.bdd_mul hM1m.aestronglyMeasurable (Filter.Eventually.of_forall hM1b)
  have ham : Measurable (fun ξ => mStarF u ξ * varphiN N k₁ ξ) := hM1m.mul hAm
  have hbi : Integrable (fun ξ => mStargF P.natDegree u ξ * varphitildeN P.natDegree N k₂ ξ) :=
    hBi.bdd_mul hM2m.aestronglyMeasurable (Filter.Eventually.of_forall hM2b)
  have hbm : Measurable (fun ξ => mStargF P.natDegree u ξ * varphitildeN P.natDegree N k₂ ξ) :=
    hM2m.mul hBm
  trans ∫ t in (1 / 2 : ℝ)..1,
      cw (fun ξ => (mStarF u ξ * varphiN N k₁ ξ) * ee (((N : ℝ) * t) * ξ)) j₁
        * cw (fun ξ => (mStargF P.natDegree u ξ * varphitildeN P.natDegree N k₂ ξ)
            * ee ((PevalR P ((N : ℝ) * t)) * ξ)) j₂
  · refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (fun ξ => mStarF u ξ * varphiNt N k₁ t ξ)
        = fun ξ => (mStarF u ξ * varphiN N k₁ ξ) * ee (((N : ℝ) * t) * ξ) := by
      funext ξ
      simp only [varphiNt]
      ring
    have h2 : (fun ξ => mStargF P.natDegree u ξ * varphitildeNt P P.natDegree N k₂ t ξ)
        = fun ξ => (mStargF P.natDegree u ξ * varphitildeN P.natDegree N k₂ ξ)
            * ee ((PevalR P ((N : ℝ) * t)) * ξ) := by
      funext ξ
      simp only [varphitildeNt]
      ring
    rw [h1, h2]
  trans ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ,
      (mStarF u ξ₁ * varphiN N k₁ ξ₁)
        * (mStargF P.natDegree u ξ₂ * varphitildeN P.natDegree N k₂ ξ₂)
        * (∫ t in (1 / 2 : ℝ)..1,
            ee (((N : ℝ) * t) * ξ₁ + (PevalR P ((N : ℝ) * t)) * ξ₂))
        * ee (-(j₁ : ℝ) * ξ₁ - (j₂ : ℝ) * ξ₂)
  · exact Work.A7.cw_interval_integral_fubini
      (a := fun ξ => mStarF u ξ * varphiN N k₁ ξ)
      (b := fun ξ => mStargF P.natDegree u ξ * varphitildeN P.natDegree N k₂ ξ)
      (u := fun t : ℝ => (N : ℝ) * t) (v := fun t : ℝ => PevalR P ((N : ℝ) * t))
      hai hbi ham hbm (by fun_prop) (by unfold PevalR; fun_prop) j₁ j₂
  · have harg : ∀ θ₁ θ₂ : ℝ,
        -(j₁ : ℝ) * θ₁ - (j₂ : ℝ) * θ₂ = -((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂) :=
      fun θ₁ θ₂ => by ring
    simp only [harg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
    dsimp only
    rw [Work.A7.mTilde_eq_phase P N ξ₁ ξ₂]
    ring

end Work.KMTAreas.A7
