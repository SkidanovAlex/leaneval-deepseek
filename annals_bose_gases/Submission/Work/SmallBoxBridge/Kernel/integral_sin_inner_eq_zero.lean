import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Kernel

open MeasureTheory

/-- The sine weight `p ↦ sin ⟪p, z⟫` is odd, while the radial factor `F ‖p‖` is even:
hence the integrand `p ↦ F ‖p‖ * sin ⟪p, z⟫` is odd under `p ↦ -p`.  As the Lebesgue
measure on `ℝ³` is invariant under negation, the integral over all of `ℝ³` vanishes. -/
theorem integral_sin_inner_eq_zero (F : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * Real.sin (inner ℝ p z)) = 0 := by
  -- the integrand is odd
  have hodd : ∀ p : EuclideanSpace ℝ (Fin 3),
      F ‖-p‖ * Real.sin (inner ℝ (-p) z) = -(F ‖p‖ * Real.sin (inner ℝ p z)) := by
    intro p
    rw [norm_neg, inner_neg_left, Real.sin_neg]
    ring
  -- the integral is invariant under `p ↦ -p`
  have h1 : (∫ p : EuclideanSpace ℝ (Fin 3), F ‖-p‖ * Real.sin (inner ℝ (-p) z)) =
      ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * Real.sin (inner ℝ p z) :=
    integral_neg_eq_self (fun p : EuclideanSpace ℝ (Fin 3) =>
      F ‖p‖ * Real.sin (inner ℝ p z)) volume
  rw [funext hodd] at h1
  -- `∫ -f = -∫ f`
  rw [integral_neg] at h1
  -- so `-I = I`, hence `I = 0`
  exact (self_eq_neg).mp h1.symm

end Work.SmallBoxBridge.Kernel
