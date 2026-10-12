import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsW_le_L2_Dir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.hlocWire2

open MeasureTheory

/-- **Monotonicity of the `F`-weighted `p`-space kinetic form in the symbol bound.**

If the radial symbol `F` is nonnegative and globally bounded by the constant `A`, then the
`F`-weighted kinetic form of a smooth compactly supported state `u`,
`(2π)⁻³·bsW F u = (2π)⁻³ ∫_p F(‖p‖)·‖kinFT u p‖²`, is dominated by `A` times the `L²` mass
`bsL2 u = ∫_x u(x)²` of `u`.

The proof is one comparison of integrals together with the (`p`-convention) Plancherel identity
(`Work.BSKinetic.plancherel_pconv`): pointwise `F(‖p‖) ≤ A` gives
`∫_p F(‖p‖)‖kinFT u p‖² ≤ A ∫_p ‖kinFT u p‖²`, the dominating integrand is integrable because
`p ↦ ‖kinFT u p‖² ∈ L¹` (`Work.BSKinetic.integrable_kinFT_sq`) and `A` is a constant, and
`(2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x u(x)² = bsL2 u`. -/
theorem bsW_le_of_le_const {F : ℝ → ℝ} {A : ℝ} (hF0 : ∀ r : ℝ, 0 ≤ F r)
    (hFA : ∀ r : ℝ, F r ≤ A) {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F u
      ≤ A * Work.BSKinetic.Decomp.bsL2 u := by
  have hpre : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  -- `p ↦ ‖kinFT u p‖²` is integrable, hence so is its `A`-multiple.
  have hInt : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq u hu hcs
  have hmajor : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      A * ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2) :=
    hInt.const_mul A
  -- the pointwise symbol bound `F(‖p‖) ≤ A` passes to the `p`-integral
  have hmono : (∫ p : EuclideanSpace ℝ (Fin 3),
        F ‖p‖ * ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2)
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3),
        A * ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_) hmajor
      (Filter.Eventually.of_forall fun p => ?_)
    · exact mul_nonneg (hF0 ‖p‖) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hFA ‖p‖) (sq_nonneg _)
  have hpl := Work.BSKinetic.plancherel_pconv u hu hcs
  have hbsL2 : Work.BSKinetic.Decomp.bsL2 u = ∫ z : EuclideanSpace ℝ (Fin 3), (u z) ^ 2 := rfl
  rw [Work.BSKinetic.Decomp.bsW]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          F ‖p‖ * ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          A * ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hpre
    _ = A * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2)) := by
        rw [integral_const_mul]; ring
    _ = A * (∫ z : EuclideanSpace ℝ (Fin 3), (u z) ^ 2) := by rw [hpl]
    _ = A * Work.BSKinetic.Decomp.bsL2 u := by rw [hbsL2]

end Work.hlocWire2
