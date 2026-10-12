import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Resolve

open MeasureTheory

/-- The kinetic kernel `K_F(z) = (2π)⁻³∫_p F(‖p‖)cos⟪p,z⟫dp` is (a.e.) strongly measurable.

Since `F` is only assumed measurable along the composition `p ↦ F ‖p‖` (through integrability),
the proof replaces `p ↦ F ‖p‖` by a measurable representative `g` agreeing with it a.e.; then
`z ↦ ∫_p g p·cos⟪p,z⟫dp` is continuous by dominated convergence (dominated by `‖g‖ ∈ L¹`), and
`K_F` agrees with `(2π)⁻³` times it pointwise. -/
theorem kinKernel_aestronglyMeasurable (F : ℝ → ℝ)
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖)) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinKernel F z) MeasureTheory.volume := by
  have hφ_meas : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖) volume := hF.aemeasurable
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := hφ_meas.mk (fun p => F ‖p‖)
  have hg_meas : Measurable g := hφ_meas.measurable_mk
  have hg_ae : (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖) =ᵐ[volume] g := hφ_meas.ae_eq_mk
  have hg_int : Integrable g volume := hF.congr hg_ae
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ p : EuclideanSpace ℝ (Fin 3), g p * Real.cos (inner ℝ p z)) := by
    refine MeasureTheory.continuous_of_dominated (bound := fun p => ‖g p‖) ?_ ?_ hg_int.norm ?_
    · intro z
      exact (hg_meas.mul (by fun_prop :
        Continuous fun p : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ p z)).measurable).aestronglyMeasurable
    · intro z
      filter_upwards with p
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z))
    · filter_upwards with p
      exact continuous_const.mul (by fun_prop)
  refine (hcont.aestronglyMeasurable.const_mul (((2 * Real.pi) ^ 3)⁻¹)).congr ?_
  filter_upwards with z
  simp only [Submission.BoseGases.kinKernel]
  congr 1
  exact integral_congr_ae (hg_ae.mul (Filter.Eventually.of_forall fun p => rfl)).symm

end Work.SmallBoxBridge.Resolve
