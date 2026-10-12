import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.SqrtKin.subordination_t_p_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.continuum_heatSubordination_v2`

The **corrected** continuum heat-subordination identity of Fournais–Solovej: with the momentum
integrals properly parenthesised (see
`Submission/Work/BoseBoxFock/FINDING_continuum_heatSubordination_FALSE.md` for why the
unparenthesised version is false — Lean parses the body of `∫ p, ·` below `-`, so the bracket
must be `(∫ p, ‖kinFT g p‖²) - (∫ p, e^{-t‖p‖²}‖kinFT g p‖²)`) the identity reads

`(2π)^{-3}∫_p ‖p‖‖kinFT g p‖² = (2√π)^{-1} ∫_0^∞ t^{-3/2}(kinMass g − kinHeat g t)dt`,

which is the true relation `√a = (2√π)^{-1}∫_0^∞ t^{-3/2}(1 − e^{-at})dt` integrated over momenta.

The mathematical content is exactly `Submission.Work.BoseBoxFock.SqrtKin.subordination_t_p_swap`
(`∫_0^∞ t^{-3/2}(kinMass g − kinHeat g t)dt = 2√π·kinFirst g`); the work here is only to
match the two spellings of the heat-regularised momentum integral
(`kinHeat` uses `Real.exp (-(t * ‖p‖ ^ 2))`, the target uses `Real.exp (-t * ‖p‖ ^ 2)`)
and to divide by `2√π`.
-/

noncomputable section

open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem continuum_heatSubordination_v2 {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) :
    ((2*Real.pi)^3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖^2
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
            ( ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                ‖Submission.BoseGases.kinFT g p‖^2)
             - ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
                Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2) ) := by
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (ℓ/2))
      (isCompact_closedBall 0 (ℓ/2)) ?_
    exact (subset_tsupport g).trans (hgsupp.trans Metric.ball_subset_closedBall)
  have hkey := SqrtKin.subordination_t_p_swap (g := g) hg hcs
  have hheat : ∀ t : ℝ,
      kinHeat g t = ((2*Real.pi)^3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2 := by
    intro t
    unfold kinHeat
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with p
    simp only [neg_mul]
  have hInt : (∫ t in Set.Ioi 0, t^(-3/2:ℝ) * (kinMass g - kinHeat g t))
      = ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
          ( ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
              ‖Submission.BoseGases.kinFT g p‖^2)
           - ((2*Real.pi)^3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
              Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2) ) := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with t ht
    unfold kinMass
    rw [hheat t]
  rw [← hInt, hkey]
  change kinFirst g = (2 * Real.sqrt Real.pi)⁻¹ * (2 * Real.sqrt Real.pi * kinFirst g)
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Work.BoseBoxFock
