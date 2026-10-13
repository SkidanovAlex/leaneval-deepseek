import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp2
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.integrable_lambVector_kernel
import Submission.Work.FTS.PressureOn.PoissonAux.integrable_smul_newtonGrad
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

open FiniteTimeSingularity Set MeasureTheory Metric Gradient
open scoped Topology

theorem weakPoisson {f : R3 → R3} (hf : Continuous f) (hcs : HasCompactSupport f)
    {φ : R3 → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφcs : HasCompactSupport φ) :
    ∫ x, pressurePotential f x * laplaceTrace φ x
      = ∫ x, inner ℝ (f x) (gradient φ x) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ 2
  have hΔcont : Continuous (laplaceTrace φ) := Green.continuous_laplaceTrace φ hφ2
  have hΔcs : HasCompactSupport (laplaceTrace φ) := hφcs.mono' (by
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (Green.laplaceTrace_eq_zero_of_notMem_tsupport hxt))
  -- the joint integrand of the double integral
  have hint : Integrable (fun p : R3 × R3 =>
      inner ℝ (newtonGrad (p.1 - p.2)) (f p.2) * laplaceTrace φ p.1) :=
    PoissonAux.integrable_lambVector_kernel hf hcs hφ2 hφcs
  -- the inner integral, for each `y`
  have hper : ∀ y : R3,
      ∫ x, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x
        = inner ℝ (f y) (gradient φ y) := by
    intro y
    have hInt : Integrable (fun x : R3 => laplaceTrace φ x • newtonGrad (x - y)) :=
      PoissonAux.integrable_smul_newtonGrad hΔcont hΔcs y
    have hpt : ∀ x : R3, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x
        = (innerSL ℝ (f y)) (laplaceTrace φ x • newtonGrad (x - y)) := by
      intro x
      rw [innerSL_apply_apply, inner_smul_right, real_inner_comm, mul_comm]
    calc ∫ x, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x
        = ∫ x, (innerSL ℝ (f y)) (laplaceTrace φ x • newtonGrad (x - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (innerSL ℝ (f y)) (∫ x, laplaceTrace φ x • newtonGrad (x - y)) :=
          ContinuousLinearMap.integral_comp_comm _ hInt
      _ = inner ℝ (f y) (gradient φ y) := by
          rw [PoissonAux.kernelGradIntegral hφ hφcs y, innerSL_apply_apply]
  have hfun : (fun x : R3 => pressurePotential f x * laplaceTrace φ x)
      = fun x : R3 => ∫ y, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x := by
    funext x
    rw [pressurePotential_eq_integral_newtonGrad, MeasureTheory.integral_mul_const]
  calc ∫ x, pressurePotential f x * laplaceTrace φ x
      = ∫ x, ∫ y, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x := by
        rw [hfun]
    _ = ∫ y, ∫ x, inner ℝ (newtonGrad (x - y)) (f y) * laplaceTrace φ x :=
        MeasureTheory.integral_integral_swap hint
    _ = ∫ y, inner ℝ (f y) (gradient φ y) :=
        integral_congr_ae (Filter.Eventually.of_forall hper)

end Work.FTS.PressureOn
