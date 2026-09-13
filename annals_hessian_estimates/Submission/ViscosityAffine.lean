/-
Viscosity solutions are preserved by subtracting an affine function, and the Hessian operator
`HessOp` is additive and vanishes on affine functions.  These facts are needed in Section 3 of
Shankar--Yuan, where the weighted gradient estimate is applied to `u - (u(x) + Du(x)·(y - x))`.
-/
import Mathlib
import Submission.Viscosity
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_sub_of_mem_nhds
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_neg_of_mem_nhds

open MeasureTheory Metric Set Filter Function
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The Hessian operator is additive. -/
theorem hessOp_add_of_mem_nhds {φ ψ : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴} (hs : s ∈ 𝓝 x)
    (hφ : ContDiffWithinAt ℝ 2 φ s x) (hψ : ContDiffWithinAt ℝ 2 ψ s x) :
    HessOp (φ + ψ) s x = HessOp φ s x + HessOp ψ s x := by
  have hsub : HessOp (φ - (-ψ)) s x = HessOp φ s x - HessOp (-ψ) s x := by
    unfold HessOp
    exact hessianWithin_sub_of_mem_nhds hs hφ hψ.neg
  have h3 : HessOp (φ + ψ) s x = HessOp (φ - (-ψ)) s x := by
    congr 1
    funext y
    simp
  have h4 : HessOp (-ψ) s x = - HessOp ψ s x := by
    unfold HessOp
    exact hessianWithin_neg_of_mem_nhds hs
  rw [h3, hsub, h4]
  abel

/-- The Hessian operator of an affine function vanishes. -/
theorem hessOp_affine (c : ℝ) (L : ℝ⁴ →L[ℝ] ℝ) {s : Set ℝ⁴} {x : ℝ⁴} (hs : s ∈ 𝓝 x) :
    HessOp (fun y => c + L y) s x = 0 := by
  unfold HessOp
  rw [hessianWithin_eq_hessian (u := fun y : ℝ⁴ => c + L y) hs]
  have h : fderiv ℝ (fun y : ℝ⁴ => c + L y) = fun _ => L := by
    funext y
    exact ((L.hasFDerivAt).const_add c).fderiv
  rw [h]
  simp

/-- Viscosity subsolutions are preserved by subtracting an affine function. -/
theorem isViscSubsolution_sub_affine {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    (hs : IsOpen s) (hu : IsViscSubsolution F u s) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) :
    IsViscSubsolution F (fun y => u y - (c + L y)) s := by
  intro φ hφ x hx hloc
  have haff : ContDiffOn ℝ 2 (fun y : ℝ⁴ => c + L y) s := by fun_prop
  have hφ' : ContDiffOn ℝ 2 (fun y : ℝ⁴ => φ y + (c + L y)) s := hφ.add haff
  have hloc' : ∀ᶠ y in 𝓝[s] x,
      u y - (fun y : ℝ⁴ => φ y + (c + L y)) y ≤ u x - (fun y : ℝ⁴ => φ y + (c + L y)) x := by
    filter_upwards [hloc] with y hy
    linarith [hy]
  have h := hu (fun y : ℝ⁴ => φ y + (c + L y)) hφ' x hx hloc'
  have hhess : HessOp (fun y : ℝ⁴ => φ y + (c + L y)) s x = HessOp φ s x := by
    rw [show (fun y : ℝ⁴ => φ y + (c + L y)) = φ + (fun y : ℝ⁴ => c + L y) from rfl]
    rw [hessOp_add_of_mem_nhds (hs.mem_nhds hx) (hφ.contDiffWithinAt hx)
      (haff.contDiffWithinAt hx), hessOp_affine c L (hs.mem_nhds hx), add_zero]
  rwa [hhess] at h

/-- Viscosity supersolutions are preserved by subtracting an affine function. -/
theorem isViscSupersolution_sub_affine {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    (hs : IsOpen s) (hu : IsViscSupersolution F u s) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) :
    IsViscSupersolution F (fun y => u y - (c + L y)) s := by
  intro φ hφ x hx hloc
  have haff : ContDiffOn ℝ 2 (fun y : ℝ⁴ => c + L y) s := by fun_prop
  have hφ' : ContDiffOn ℝ 2 (fun y : ℝ⁴ => φ y + (c + L y)) s := hφ.add haff
  have hloc' : ∀ᶠ y in 𝓝[s] x,
      u y - (fun y : ℝ⁴ => φ y + (c + L y)) y ≥ u x - (fun y : ℝ⁴ => φ y + (c + L y)) x := by
    filter_upwards [hloc] with y hy
    linarith [hy]
  have h := hu (fun y : ℝ⁴ => φ y + (c + L y)) hφ' x hx hloc'
  have hhess : HessOp (fun y : ℝ⁴ => φ y + (c + L y)) s x = HessOp φ s x := by
    rw [show (fun y : ℝ⁴ => φ y + (c + L y)) = φ + (fun y : ℝ⁴ => c + L y) from rfl]
    rw [hessOp_add_of_mem_nhds (hs.mem_nhds hx) (hφ.contDiffWithinAt hx)
      (haff.contDiffWithinAt hx), hessOp_affine c L (hs.mem_nhds hx), add_zero]
  rwa [hhess] at h

/-- Viscosity solutions are preserved by subtracting an affine function. -/
theorem isViscSolution_sub_affine {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    (hs : IsOpen s) (hu : IsViscSolution F u s) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) :
    IsViscSolution F (fun y => u y - (c + L y)) s :=
  ⟨isViscSubsolution_sub_affine hs hu.1 L c, isViscSupersolution_sub_affine hs hu.2 L c⟩

end Submission
