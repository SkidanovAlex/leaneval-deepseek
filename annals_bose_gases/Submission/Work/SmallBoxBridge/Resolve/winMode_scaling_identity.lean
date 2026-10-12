import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.SmallBoxBridge.Resolve

/-- Scaling identity for the `p`-mode kinetic word: the change of variables `p = 2π·ξ`
turns the `(2π)⁻³ ∫_p ‖p‖² g((2π)⁻¹ p)` normalization into `(2π)² ∫_ξ ‖ξ‖² g(ξ)`.

This is the elementary bookkeeping behind the identification of the `p`-convention
kinetic word `(2π)⁻³∫_p [‖p‖−c]₊²·(…)` with its `ξ`-convention twin. -/
theorem winMode_scaling_identity (g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    ((2 * Real.pi) ^ 3)⁻¹
        * (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * g ((2 * Real.pi)⁻¹ • p))
      = (2 * Real.pi) ^ 2 * (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖ξ‖ ^ 2 * g ξ) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hne : (2:ℝ) * Real.pi ≠ 0 := hpi.ne'
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖(2 * Real.pi) • x‖ ^ 2 = (2 * Real.pi)^2 * ‖x‖^2 := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi]
    ring
  let h : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ‖(2 * Real.pi) • x‖ ^ 2 * g x
  have step1 : (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * g ((2 * Real.pi)⁻¹ • p))
      = ∫ p : EuclideanSpace ℝ (Fin 3), h ((2 * Real.pi)⁻¹ • p) := by
    congr 1 with p
    simp only [h]
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  have step2 : (∫ p : EuclideanSpace ℝ (Fin 3), h ((2 * Real.pi)⁻¹ • p))
      = (2 * Real.pi) ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3), h x) := by
    rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume h hpi.le]
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp [EuclideanSpace],
      smul_eq_mul]
  have step3 : (∫ x : EuclideanSpace ℝ (Fin 3), h x)
      = (2 * Real.pi) ^ 2 * (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖ξ‖ ^ 2 * g ξ) := by
    have hfun : h = fun x : EuclideanSpace ℝ (Fin 3) => (2*Real.pi)^2 * (‖x‖^2 * g x) := by
      funext x
      simp only [h]
      rw [hnorm x]
      ring
    rw [hfun, integral_const_mul]
  have hmain : (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * g ((2 * Real.pi)⁻¹ • p))
      = (2 * Real.pi) ^ 3
          * ((2 * Real.pi) ^ 2 * (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖ξ‖ ^ 2 * g ξ)) := by
    rw [step1, step2, step3]
  rw [hmain, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hne), one_mul]

end Work.SmallBoxBridge.Resolve
