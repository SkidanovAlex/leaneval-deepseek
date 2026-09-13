/-
Subtracting an affine function does not change the second derivative data of a `C²` function.
This is used in `Submission.AlexandrovLimit` to apply the classical weighted gradient estimate
to the affine-corrected functions `u - (c + L ·)`.
-/
import Mathlib
import Submission.Viscosity
import Submission.ViscosityAffine
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_trace_hessian

open HessianEstimates
open Laplacian Metric MeasureTheory Set Filter
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The Hessian operator is unchanged by subtracting an affine function. -/
theorem H_sub_affine {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {z : ℝ⁴} (hs : s ∈ 𝓝 z)
    (hu : ContDiffWithinAt ℝ 2 u s z) (c : ℝ) (L : ℝ⁴ →L[ℝ] ℝ) :
    H (fun y : ℝ⁴ => u y - (c + L y)) s z = H u s z := by
  have haff : ContDiffWithinAt ℝ 2 (fun y : ℝ⁴ => c + L y) s z := by fun_prop
  have hsub : HessOp (fun y : ℝ⁴ => u y - (c + L y)) s z
      = HessOp u s z - HessOp (fun y : ℝ⁴ => c + L y) s z := by
    unfold HessOp
    exact hessianWithin_sub_of_mem_nhds hs hu haff
  have h0 : HessOp (fun y : ℝ⁴ => c + L y) s z = 0 := hessOp_affine c L hs
  show HessOp (fun y : ℝ⁴ => u y - (c + L y)) s z = HessOp u s z
  rw [hsub, h0, sub_zero]

/-- The Laplacian is unchanged by subtracting an affine function. -/
theorem laplacian_sub_affine {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {z : ℝ⁴} (hs : IsOpen s) (hz : z ∈ s)
    (hu : ContDiffOn ℝ 3 u s) (c : ℝ) (L : ℝ⁴ →L[ℝ] ℝ) :
    (Δ (fun y : ℝ⁴ => u y - (c + L y))) z = (Δ u) z := by
  have hcont : ContDiffOn ℝ 2 (fun y : ℝ⁴ => u y - (c + L y)) s := by
    exact (hu.of_le (by norm_num)).sub (by fun_prop)
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hfin : Module.finrank ℝ ℝ⁴ = 4 := by simp [finrank_euclideanSpace]
  rw [laplacian_eq_trace_hessian hs hz hcont
        ((EuclideanSpace.basisFun (Fin 4) ℝ).reindex (finCongr hfin.symm)),
    laplacian_eq_trace_hessian hs hz hu2
        ((EuclideanSpace.basisFun (Fin 4) ℝ).reindex (finCongr hfin.symm))]
  rw [show (InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ (fun y : ℝ⁴ => u y - (c + L y)) s) s z))
      = H (fun y : ℝ⁴ => u y - (c + L y)) s z from rfl,
    show (InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s z)) = H u s z from rfl,
    H_sub_affine (hs.mem_nhds hz) (hu2.contDiffWithinAt hz) c L]

/-- `σ₂` is unchanged by subtracting an affine function. -/
theorem sigma2_sub_affine {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {z : ℝ⁴} (hs : s ∈ 𝓝 z)
    (hu : ContDiffWithinAt ℝ 2 u s z) (c : ℝ) (L : ℝ⁴ →L[ℝ] ℝ) :
    σ₂ (H (fun y : ℝ⁴ => u y - (c + L y)) s z) = σ₂ (H u s z) := by
  rw [H_sub_affine hs hu c L]

end Submission
