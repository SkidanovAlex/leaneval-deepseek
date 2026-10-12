import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `K_F` is (everywhere) strongly measurable

The kinetic kernel `kinKernel F z = (2π)⁻³∫_p F(‖p‖)cos⟪p,z⟫dp` is strongly measurable as a
function of `z`, under the only hypothesis available: the radial symbol `p ↦ F ‖p‖` is
integrable (so it is *a.e.* strongly measurable, but not necessarily *everywhere* measurable —
`F` itself is an arbitrary function `ℝ → ℝ`).

The point of the argument is that the value of the integral at a *fixed* `z` depends on `F`
only through the a.e. class of `p ↦ F ‖p‖` (multiplying by the bounded measurable function
`p ↦ cos⟪p,z⟫` preserves a.e. equality).  Hence, replacing `p ↦ F ‖p‖` by a measurable
representative `g` (agreeing with it a.e.), the kernel becomes

  `kinKernel F z = (2π)⁻³ ∫_p g p · cos⟪p,z⟫ dp   for **every** z`,

and the right-hand side is continuous in `z` by dominated convergence, dominated by
`‖g‖ ∈ L¹`.  This is *pointwise* (not merely a.e.) equality, which is what upgrades the
a.e. statement `kinKernel_aestronglyMeasurable` to genuine strong measurability: a.e. equality
alone does not preserve `StronglyMeasurable` (the function may be altered on a non-measurable
null set), so the integral representation must be used at each point.
-/

namespace Work.SmallBoxBridge.Resolve

open MeasureTheory

theorem kinKernel_stronglyMeasurable {F : ℝ → ℝ}
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖)) :
    MeasureTheory.StronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinKernel F z) := by
  -- a measurable representative of the radial symbol
  have hφ_meas : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖) volume := hF.aemeasurable
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := hφ_meas.mk (fun p => F ‖p‖)
  have hg_meas : Measurable g := hφ_meas.measurable_mk
  have hg_ae : (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖) =ᵐ[volume] g := hφ_meas.ae_eq_mk
  have hg_int : Integrable g volume := hF.congr hg_ae
  -- the integral against `g` is continuous in `z`, by dominated convergence
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ p : EuclideanSpace ℝ (Fin 3), g p * Real.cos (inner ℝ p z)) := by
    refine MeasureTheory.continuous_of_dominated (bound := fun p => ‖g p‖) ?_ ?_ hg_int.norm ?_
    · intro z
      exact (hg_meas.mul (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
        Real.cos (inner ℝ p z)).measurable).aestronglyMeasurable
    · intro z
      filter_upwards with p
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z))
    · filter_upwards with p
      exact continuous_const.mul (by fun_prop)
  -- pointwise identification of the kernel with that continuous function
  have hkey : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinKernel F z =
        ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), g p * Real.cos (inner ℝ p z) := by
    intro z
    rw [Submission.BoseGases.kinKernel]
    congr 1
    exact MeasureTheory.integral_congr_ae (hg_ae.mul (Filter.Eventually.of_forall fun p => rfl))
  rw [funext hkey]
  exact (hcont.const_mul _).stronglyMeasurable

end Work.SmallBoxBridge.Resolve
