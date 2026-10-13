/-
# The gradient form of the fundamental-solution identity for `-Δ`

The target statement is the *gradient* version of `Δ(1/(4π‖x‖)) = -δ₀`:

  `∫ x, laplaceTrace ψ x • newtonGrad (x - y) = gradient ψ y`

for `ψ : ℝ³ → ℝ` of class `C^∞` with compact support.

The proof reduces to the centred scalar identity
`∫ z, laplaceTrace Ψ z * ∂ᵢ newtonKernel z = ∂ᵢΨ 0` (proved in `kernelGradAux2` by regularising the
Newtonian kernel and passing to the limit), assembles the vector identity from its coordinates, and
translates the result.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

open kgiAux

/-! ## The centred vector identity -/

/-- **The centred vector identity**: `∫ ΔΨ • ∇N = ∇Ψ(0)`. -/
theorem kernelGrad_centred {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hcs : HasCompactSupport Ψ) :
    ∫ z, laplaceTrace Ψ z • newtonGrad z = gradient Ψ 0 := by
  have hint : Integrable (fun z : R3 => laplaceTrace Ψ z • newtonGrad z) :=
    integrable_smul_newtonGrad (Work.FTS.PressureOn.Green.continuous_laplaceTrace Ψ (hΨ 2))
      (hasCompactSupport_laplaceTrace hcs)
  refine PiLp.ext fun i => ?_
  have hcoord : inner ℝ (FiniteTimeSingularity.e i) (∫ z, laplaceTrace Ψ z • newtonGrad z)
      = inner ℝ (FiniteTimeSingularity.e i) (gradient Ψ 0) := by
    have h1 : inner ℝ (FiniteTimeSingularity.e i) (∫ z, laplaceTrace Ψ z • newtonGrad z)
        = ∫ z, inner ℝ (FiniteTimeSingularity.e i) (laplaceTrace Ψ z • newtonGrad z) := by
      simpa only [innerSL_apply_apply] using
        (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (FiniteTimeSingularity.e i))
          hint).symm
    rw [h1]
    have h2 : (fun z : R3 => inner ℝ (FiniteTimeSingularity.e i)
          (laplaceTrace Ψ z • newtonGrad z))
        = fun z : R3 => laplaceTrace Ψ z * inner ℝ (FiniteTimeSingularity.e i) (newtonGrad z) := by
      funext z
      rw [inner_smul_right]
    rw [h2]
    have h3 : (fun z : R3 => laplaceTrace Ψ z * inner ℝ (FiniteTimeSingularity.e i)
          (newtonGrad z))
        = fun z : R3 => laplaceTrace Ψ z * fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i) := by
      funext z
      rw [inner_e_newtonGrad_tmp z i]
    rw [h3, kernelGrad_coord hΨ hcs i, real_inner_comm]
    exact inner_gradient_left.symm
  rw [← Work.FTS.PressureOn.Green.inner_e_eq' (∫ z, laplaceTrace Ψ z • newtonGrad z) i,
    ← Work.FTS.PressureOn.Green.inner_e_eq' (gradient Ψ 0) i]
  exact hcoord

theorem kernelGradIntegral {ψ : R3 → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hcs : HasCompactSupport ψ)
    (y : R3) :
    ∫ x, laplaceTrace ψ x • newtonGrad (x - y) = gradient ψ y := by
  have hshift : ∫ x, laplaceTrace ψ x • newtonGrad (x - y)
      = ∫ z, laplaceTrace ψ (y + z) • newtonGrad z := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun w : R3 => laplaceTrace ψ w • newtonGrad (w - y)) y]
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [add_sub_cancel_left]
  rw [hshift]
  have hΨ : ∀ n : ℕ, ContDiff ℝ n (fun z : R3 => ψ (y + z)) := fun n =>
    (hψ n).comp (contDiff_const.add contDiff_id)
  have hcsΨ : HasCompactSupport (fun z : R3 => ψ (y + z)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun w : R3 => w - y) '' tsupport ψ)
      (hcs.image (continuous_id.sub continuous_const)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    refine ⟨y + z, ?_, by simp⟩
    by_contra h
    exact hz (by rw [image_eq_zero_of_notMem_tsupport h])
  calc ∫ z, laplaceTrace ψ (y + z) • newtonGrad z
      = ∫ z, laplaceTrace (fun z' : R3 => ψ (y + z')) z • newtonGrad z := by
        refine integral_congr_ae ?_
        filter_upwards with z
        rw [laplaceTrace_comp_add ψ y z]
    _ = gradient (fun z : R3 => ψ (y + z)) 0 := kernelGrad_centred hΨ hcsΨ
    _ = gradient ψ y := gradient_comp_add_const ψ y

end Work.FTS.PressureOn.PoissonAux
