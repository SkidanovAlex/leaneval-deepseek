import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_GaussFacts
import Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³` is a probability density

`Work.FTS.PressureOn.Auxiliary.heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` is integrable and
integrates to `1` (for `t > 0`).

The integral was already computed in the sibling module
`Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel`
(`integral_heatKernel t ht : ∫ z, heatKernel t z = 1`); here we only add the integrability, which
is the observation that the heat kernel is a *constant* times the Gaussian
`z ↦ exp (-((4t)⁻¹ ‖z‖²))`, and Gaussians are integrable (`ihak_integrable_rexp_normSq`).
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **Integrability of the heat kernel.**  For `t > 0` the kernel is the constant
`(4πt)^{-3/2}` times the Gaussian `z ↦ exp (-(4t)⁻¹‖z‖²)`, and the Gaussian is integrable on
`ℝ³`. -/
private lemma integrable_heatKernel_aux {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  have ha : (0 : ℝ) < (4 * t)⁻¹ := inv_pos.mpr (by linarith)
  have hbase : Integrable (fun z : R3 => Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2))) :=
    ihak_integrable_rexp_normSq ((4 * t)⁻¹) ha
  refine (hbase.const_mul ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))).congr
    (Filter.Eventually.of_forall fun z => ?_)
  exact (heatKernel_eq_const_mul_exp ht z).symm

theorem heatKernel_integral_one (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable (Work.FTS.PressureOn.Auxiliary.heatKernel t) ∧
      (∫ z : Work.FTS.PressureOn.R3, Work.FTS.PressureOn.Auxiliary.heatKernel t z) = 1 :=
  ⟨integrable_heatKernel_aux ht, integral_heatKernel t ht⟩

end

end Work.FTS.PressureOn.Auxiliary
