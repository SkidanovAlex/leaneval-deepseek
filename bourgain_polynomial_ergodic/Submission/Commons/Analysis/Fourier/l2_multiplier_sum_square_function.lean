import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_l2

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform ENNReal BigOperators Topology

set_option maxHeartbeats 1000000

/-- **`L²` sum-of-squares bound for a countable family of multipliers.**

The `∑'` companion of `Commons.Analysis.Fourier.BoundaryLayer.l2_multiplier_square_function`:
if the squared moduli of a countable family `m` of essentially bounded symbols are pointwise
summable with bound `A²`, then the *sum* of the squared `L²`-norms of the associated multiplier
operators is at most `A²‖f‖²`.  Equivalently the "dyadic values square function"
`(∑_i |𝓕⁻[m_i·𝓕f]|²)^{1/2}` is in `L²` with norm at most `A‖f‖`; this is Bourgain (1989),
(3.14). -/
theorem l2_multiplier_sum_square_function {ι : Type*} [Countable ι]
    (m : ι → ℝ → ℂ) (hm : ∀ i, MemLp (m i) ⊤ (volume : Measure ℝ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (A : ℝ)
    (hA : ∀ ξ, (∑' i, ‖m i ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A^2)) :
    ∫⁻ x, (∑' i, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal (A^2) * ‖f‖ₑ ^ (2:ℝ) := by
  have hmeas : ∀ i, AEMeasurable
      (fun x => ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ))
      volume :=
    fun i => (MeasureTheory.Lp.aestronglyMeasurable
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier (m i) (hm i) f)).enorm.pow_const (2:ℝ)
  rw [lintegral_tsum hmeas]
  calc ∑' i, ∫⁻ x,
        ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier (m i) (hm i) f) x‖ₑ ^ (2:ℝ)
      = ∑' i, ∫⁻ ξ, ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply tsum_congr; intro i
        rw [← Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral
              (Commons.Analysis.Fourier.BoundaryLayer.multiplier (m i) (hm i) f),
            Commons.Analysis.Fourier.BoundaryLayer.enorm_multiplier_sq]
    _ = ∫⁻ ξ, ∑' i, ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
        (lintegral_tsum (f := fun (i : ι) (ξ : ℝ) =>
            ‖m i ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ))
          (fun i => ((hm i).aestronglyMeasurable.enorm.pow_const (2:ℝ)).mul
            ((MeasureTheory.Lp.aestronglyMeasurable (𝓕 f)).enorm.pow_const (2:ℝ)))).symm
    _ = ∫⁻ ξ, (∑' i, ‖m i ξ‖ₑ ^ (2:ℝ)) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro ξ
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (A^2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro ξ
        exact mul_le_mul' (hA ξ) le_rfl
    _ = ENNReal.ofReal (A^2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A^2) * ‖𝓕 f‖ₑ ^ (2:ℝ) := by
        rw [Commons.Analysis.Fourier.BoundaryLayer.lp_enorm_sq_eq_lintegral]
    _ = ENNReal.ofReal (A^2) * ‖f‖ₑ ^ (2:ℝ) := by
        rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_fourier]

end Commons.Analysis.Fourier
