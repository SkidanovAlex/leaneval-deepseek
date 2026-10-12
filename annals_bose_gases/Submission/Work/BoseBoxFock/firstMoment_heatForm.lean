import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.deficitAlias_heatForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory Filter Metric
open scoped Real BigOperators

/-!
# `Work.BoseBoxFock.firstMoment_heatForm`

The **heat form of the first-moment deficit**, obtained by subtracting the two already-proved
heat subordinations

* lattice side (`lattice_heatSubordination`):
  `S₁ = (2√π)⁻¹ ∫_0^∞ t^{-3/2} (S₀ − Λ(t)) dt`,  `Λ(t) = latHeat ℓ t g`,
* continuum side (`continuum_heatSubordination_v2`):
  `R₁ = (2√π)⁻¹ ∫_0^∞ t^{-3/2} (R₀ − E(t)) dt`,  `E(t) = contHeat g t`,

together with the frame identity `S₀ = R₀` (`frame_lattice_ball`, licensed by
`tsupport g ⊆ ball 0 (ℓ/2)`, which is contained in the box `boxL ℓ`).  Indeed

`R₁ − S₁ = (2√π)⁻¹ ∫_0^∞ t^{-3/2} (Λ(t) − E(t)) dt`

since the two masses agree.  The only inputs not literally in those two theorems are the
integrability of the two heat-deficit integrands `t^{-3/2}(S₀ − Λ(t))` and `t^{-3/2}(R₀ − E(t))`
on `(0,∞)` (needed to split the integral linearly) and the rewriting of the two spellings of
`exp`; both integrability statements are proved in `deficitAlias_heatForm`
(`integrableOn_heatDeficit_lat`, `integrableOn_heatDeficit_cont`).
-/

theorem firstMoment_heatForm {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) : Work.BoseBoxFock.kinFirst g - (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (Work.BoseBoxFock.latHeat ℓ t g - Work.BoseBoxFock.contHeat g t) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have hframe := frame_lattice_ball hℓ hg hgc (hgsupp.trans (ball_subset_corpusBox_boxL hℓ))
  have hlat := lattice_heatSubordination hℓ hg hgsupp
  have hcont := continuum_heatSubordination_v2 hℓ hg hgsupp
  have hu := integrableOn_heatDeficit_lat hℓ hg hgc
  have hv := integrableOn_heatDeficit_cont hg hgc
  -- the lattice subordination in the `Real.exp (-(t * x))`-spelling of `latHeat`
  have hlat' : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
            - Work.BoseBoxFock.latHeat ℓ t g) := by
    rw [hlat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (-3/2 : ℝ) = -(3/2) from by norm_num, latHeat_eq_alt ℓ t g]
  -- the continuum subordination, with `kinFirst` in place of its unfolding
  have hcont' : Work.BoseBoxFock.kinFirst g
      = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2))
            - Work.BoseBoxFock.contHeat g t) := by
    rw [show Work.BoseBoxFock.kinFirst g = ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 from rfl]
    rw [hcont]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (-3/2 : ℝ) = -(3/2) from by norm_num, contHeat_eq_alt g t]
  -- the difference of the two heat deficits is the difference of the heat contents
  have hsub : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
        ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2))
          - Work.BoseBoxFock.contHeat g t))
      - (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
            - Work.BoseBoxFock.latHeat ℓ t g))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (Work.BoseBoxFock.latHeat ℓ t g - Work.BoseBoxFock.contHeat g t) := by
    rw [← integral_sub hv hu]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    rw [← hframe]
    ring
  calc Work.BoseBoxFock.kinFirst g - (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = (2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
            ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2))
              - Work.BoseBoxFock.contHeat g t))
        - (2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
            ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
              - Work.BoseBoxFock.latHeat ℓ t g)) := by rw [hcont', hlat']
    _ = (2 * Real.sqrt Real.pi)⁻¹ * ((∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
            ((((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2))
              - Work.BoseBoxFock.contHeat g t))
          - (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
            ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
              - Work.BoseBoxFock.latHeat ℓ t g))) := by ring
    _ = (2 * Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (Work.BoseBoxFock.latHeat ℓ t g - Work.BoseBoxFock.contHeat g t) := by rw [hsub]

end Work.BoseBoxFock
