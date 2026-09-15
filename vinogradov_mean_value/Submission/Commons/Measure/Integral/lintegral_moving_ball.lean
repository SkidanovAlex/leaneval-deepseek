import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Measure.Integral

open MeasureTheory Metric
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The moving-ball Fubini identity.**

Let `Φ : ℝⁿ → ℝ^d` be a linear isometry (an embedding of `ℝⁿ` as a subspace `H` of `ℝ^d`), let
`r > 0` and let `F : ℝ^d → ℝ≥0∞` be a.e.-measurable.  Then integrating `F` over the moving ball
`z + Φ '' B(0,r)` (an `n`-dimensional ball in the affine subspace `z + H`) and then over `z`
recovers the full integral of `F`, up to the volume of the `n`-dimensional ball:

  `∫⁻ z, ∫⁻ w in B(0,r), F (z + Φ w) = volume (B(0,r)) * ∫⁻ x, F x`.

This is the Fubini identity used to write a full-space integral as an average of integrals over
the translates of a subspace (Guo–Li–Yung–Zorin-Kranich, arXiv:1912.09798, equation (3.11)). -/
theorem lintegral_moving_ball (d n : ℕ) (Φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hΦ : ∀ y, ‖Φ y‖ = ‖y‖) {r : ℝ} (hr : 0 < r) (F : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hF : AEMeasurable F) :
    MeasureTheory.lintegral MeasureTheory.volume
        (fun z => MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
          (fun w => F (z + Φ w)))
      = MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
        * MeasureTheory.lintegral MeasureTheory.volume F := by
  classical
  have hΦc : Continuous Φ := Φ.continuous_of_finiteDimensional
  set μB : Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) with hμB
  have hψm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
      p.1 + Φ p.2) :=
    measurable_fst.add (hΦc.measurable.comp measurable_snd)
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.1 + Φ p.2)
      (volume.prod μB) volume := by
    refine ⟨hψm, Measure.AbsolutelyContinuous.mk ?_⟩
    intro s hs hsv
    rw [Measure.map_apply hψm hs, Measure.prod_apply_symm (hψm hs)]
    have hz : ∀ w : EuclideanSpace ℝ (Fin n),
        volume ((fun z : EuclideanSpace ℝ (Fin d) => (z, w)) ⁻¹'
          ((fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.1 + Φ p.2) ⁻¹' s))
        = 0 := by
      intro w
      rw [show (fun z : EuclideanSpace ℝ (Fin d) => (z, w)) ⁻¹'
            ((fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.1 + Φ p.2) ⁻¹' s)
          = (fun z : EuclideanSpace ℝ (Fin d) => z + Φ w) ⁻¹' s from rfl]
      rw [← Measure.map_apply (measurable_add_const (Φ w)) hs,
        MeasureTheory.map_add_right_eq_self volume (Φ w)]
      exact hsv
    rw [show (fun w : EuclideanSpace ℝ (Fin n) =>
          volume ((fun z : EuclideanSpace ℝ (Fin d) => (z, w)) ⁻¹'
            ((fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.1 + Φ p.2)
              ⁻¹' s))) = fun _ => (0 : ℝ≥0∞) from funext hz]
    exact lintegral_zero
  have hG : AEMeasurable
      (Function.uncurry (fun z : EuclideanSpace ℝ (Fin d) => fun w : EuclideanSpace ℝ (Fin n) =>
        F (z + Φ w))) (volume.prod μB) := by
    have h := AEMeasurable.comp_quasiMeasurePreserving hF hqmp
    have hcomp : (F ∘ fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.1 + Φ p.2)
        = Function.uncurry (fun z : EuclideanSpace ℝ (Fin d) =>
            fun w : EuclideanSpace ℝ (Fin n) => F (z + Φ w)) := by
      funext p; rfl
    rwa [hcomp] at h
  calc ∫⁻ z, ∫⁻ w, F (z + Φ w) ∂μB
      = ∫⁻ p, F (p.1 + Φ p.2) ∂(volume.prod μB) :=
        lintegral_lintegral (μ := volume) (ν := μB) (f := fun z w => F (z + Φ w)) hG
    _ = ∫⁻ w, ∫⁻ z, F (z + Φ w) ∂volume ∂μB :=
        lintegral_prod_symm (μ := volume) (ν := μB)
          (f := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
            F (p.1 + Φ p.2)) hG
    _ = ∫⁻ w, ∫⁻ z, F z ∂volume ∂μB := by
        refine lintegral_congr (fun w => ?_)
        exact lintegral_add_right_eq_self F (Φ w)
    _ = (∫⁻ z, F z ∂volume) * μB Set.univ := by
        rw [lintegral_const]
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) * ∫⁻ x, F x := by
        rw [hμB, Measure.restrict_apply_univ, mul_comm]

end Commons.Measure.Integral