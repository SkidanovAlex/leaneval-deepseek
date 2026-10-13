import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4

theorem zouter_abs_le {δ R M : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ M) :
    |∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ)|
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ) := by
  -- Integrability of the two outer (`z`-)slice integrals: the absolute value is handled by
  -- the same bound (the box bound `|F| ≤ M` is inherited by `|F|`).
  have hAint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound hδ hFc hF0 ⟨M, hFb⟩
  have hBint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound hδ hFc.abs
      (fun z hz θ => by rw [hF0 z hz θ, abs_zero])
      ⟨M, fun z hz θ hθ => by simpa only [abs_abs] using hFb z hz θ hθ⟩
  -- Pointwise comparison of the integrands.
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      |(Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ)|
      ≤ (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ) := by
    intro z hz
    have hgz : |∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ := by
      calc |∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ|
          ≤ ∫ θ in Work.Spaces.Iθ, |F z θ * Work.FTS.EllipticEst.thEta θ| := by
            simpa only [Real.norm_eq_abs] using
              MeasureTheory.norm_integral_le_integral_norm
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (fun θ => F z θ * Work.FTS.EllipticEst.thEta θ)
        _ = ∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
            rw [abs_mul, abs_of_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
    exact mul_le_mul_of_nonneg_left hgz (sq_nonneg _)
  -- `|∫ A| ≤ ∫ |A| ≤ ∫ B` (`norm_integral_le_integral_norm` + monotonicity).
  calc |∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ)|
      ≤ ∫ z in Work.Spaces.Iz, |(Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ)| := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
            (fun z => (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ))
    _ ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.FTS.EllipticEst.thEta θ) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) hBint ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact hpt z hz

end Work.FTS.EllipticEst.Alpha4
