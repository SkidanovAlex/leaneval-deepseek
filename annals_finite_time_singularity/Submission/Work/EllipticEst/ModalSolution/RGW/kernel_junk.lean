import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

/-- If `c` fails to be a.e. strongly measurable on `(1/2, ∞)`, then it fails on the smaller
set `(z, ∞)` for any `0 < z < 1/2`; multiplying the integrand by the (a.e. strongly measurable,
nonzero on `(z,∞)`) function `t ↦ t` recovers `c`.  Hence the integrand
`t ↦ c t * t^{-1}` is not integrable on `(z,∞)`, and the Bochner integral of a non-integrable
function is `0` by definition. -/
theorem kernel_junk {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) (hz2 : z < 1 / 2)
    (hnm : ¬ MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioi (1 / 2)))) :
    ∫ t in Set.Ioi z, c t * t ^ (-(1 : ℝ)) = 0 := by
  rw [MeasureTheory.integral_undef]
  intro h
  apply hnm
  -- `c` is a.e. strongly measurable on `(1/2, ∞)` if it is on `(z, ∞) ⊇ (1/2, ∞)`.
  refine MeasureTheory.AEStronglyMeasurable.mono_set (s := Set.Ioi (1/2)) (t := Set.Ioi z) ?_ ?_
  · intro t ht
    simp only [Set.mem_Ioi] at ht ⊢
    linarith
  · -- Multiplying the integrand `c t * t⁻¹` by `t` (nonzero on `(z,∞)`) gives back `c`.
    refine (h.aestronglyMeasurable.mul aestronglyMeasurable_id).congr ?_
    show ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi z)), (c t * t ^ (-(1 : ℝ))) * t = c t
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi)] with t ht
    simp only [Set.mem_Ioi] at ht
    have ht0 : t ≠ 0 := by linarith
    rw [Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ ht0, mul_one]

end Work.EllipticEst.ModalSolution.RGW
