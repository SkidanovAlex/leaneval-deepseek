/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Auxiliary facts for the complex-valued angular Agmon inequality

Projection identities (`Complex.reCLM`/`Complex.imCLM` commute with `deriv`), the transfer of
`ContDiffOn` to the projections, and Cauchy–Schwarz for square roots.  These are used by
`Work.FTS.EllSol.Trunc.curlAgmon`, the complex form of `thetaInterpCore`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCore
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem deriv_re_eq {F : ℝ → ℂ} {θ : ℝ} (h : DifferentiableAt ℝ F θ) :
    deriv (fun θ' => (F θ').re) θ = (deriv F θ).re := by
  have h2 : HasFDerivAt (fun θ' => (F θ').re)
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ F θ)) θ :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp θ h.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply]
  rw [← h.hasFDerivAt.hasDerivAt.deriv, Complex.reCLM_apply]

theorem deriv_im_eq {F : ℝ → ℂ} {θ : ℝ} (h : DifferentiableAt ℝ F θ) :
    deriv (fun θ' => (F θ').im) θ = (deriv F θ).im := by
  have h2 : HasFDerivAt (fun θ' => (F θ').im)
      ((Complex.imCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ F θ)) θ :=
    (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp θ h.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply]
  rw [← h.hasFDerivAt.hasDerivAt.deriv, Complex.imCLM_apply]

theorem contDiffOn_re {n : ℕ} {F : ℝ → ℂ} {s : Set ℝ} (h : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun θ => (F θ).re) s := by
  have hcomp := (Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn h
  simpa [Function.comp_def, Complex.reCLM_apply] using hcomp

theorem contDiffOn_im {n : ℕ} {F : ℝ → ℂ} {s : Set ℝ} (h : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun θ => (F θ).im) s := by
  have hcomp := (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn h
  simpa [Function.comp_def, Complex.imCLM_apply] using hcomp

/-- On the open interval, differentiating the real projection twice commutes with projecting the
second derivative. -/
theorem deriv_deriv_re_eq {F : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {θ : ℝ} (hθ : θ ∈ s)
    (hF : ContDiffOn ℝ 2 F s) :
    deriv (deriv (fun θ' => (F θ').re)) θ = (deriv (deriv F) θ).re := by
  have hJ : s ∈ 𝓝 θ := hs.mem_nhds hθ
  have h1 : DifferentiableAt ℝ F θ :=
    (hF.differentiableOn (by norm_num)).differentiableAt hJ
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) s := hF.fderiv_of_isOpen hs (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) θ :=
    (hfd.differentiableOn (by norm_num)).differentiableAt hJ
  have h3 : DifferentiableAt ℝ (deriv F) θ := by
    have he : deriv F =ᶠ[𝓝 θ] (fun θ' => (fderiv ℝ F θ') 1) := by
      filter_upwards [hJ] with θ' hθ'
      exact ((hF.differentiableOn (by norm_num)).differentiableAt
        (hs.mem_nhds hθ')).hasFDerivAt.hasDerivAt.deriv
    exact (Filter.EventuallyEq.differentiableAt_iff he).mpr
      (h2.clm_apply (differentiableAt_const (1 : ℝ)))
  have h4 : deriv (deriv (fun θ' => (F θ').re)) θ
      = deriv (fun θ' => (deriv F θ').re) θ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hJ] with θ' hθ'
    exact deriv_re_eq ((hF.differentiableOn (by norm_num)).differentiableAt
      (hs.mem_nhds hθ'))
  rw [h4]
  exact deriv_re_eq h3

/-- Same as `deriv_deriv_re_eq` for the imaginary part. -/
theorem deriv_deriv_im_eq {F : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {θ : ℝ} (hθ : θ ∈ s)
    (hF : ContDiffOn ℝ 2 F s) :
    deriv (deriv (fun θ' => (F θ').im)) θ = (deriv (deriv F) θ).im := by
  have hJ : s ∈ 𝓝 θ := hs.mem_nhds hθ
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) s := hF.fderiv_of_isOpen hs (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) θ :=
    (hfd.differentiableOn (by norm_num)).differentiableAt hJ
  have h3 : DifferentiableAt ℝ (deriv F) θ := by
    have he : deriv F =ᶠ[𝓝 θ] (fun θ' => (fderiv ℝ F θ') 1) := by
      filter_upwards [hJ] with θ' hθ'
      exact ((hF.differentiableOn (by norm_num)).differentiableAt
        (hs.mem_nhds hθ')).hasFDerivAt.hasDerivAt.deriv
    exact (Filter.EventuallyEq.differentiableAt_iff he).mpr
      (h2.clm_apply (differentiableAt_const (1 : ℝ)))
  have h4 : deriv (deriv (fun θ' => (F θ').im)) θ
      = deriv (fun θ' => (deriv F θ').im) θ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hJ] with θ' hθ'
    exact deriv_im_eq ((hF.differentiableOn (by norm_num)).differentiableAt
      (hs.mem_nhds hθ'))
  rw [h4]
  exact deriv_im_eq h3

/-- `√(a b) + √(c d) ≤ √((a+c)(b+d))` for `a,b,c,d ≥ 0`. -/
theorem sqrt_add_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have habcd : 0 ≤ a * b * (c * d) := mul_nonneg hab hcd
  have hfirst : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2
      = a * b + c * d + 2 * Real.sqrt (a * b * (c * d)) := by
    rw [add_sq, Real.sq_sqrt hab, Real.sq_sqrt hcd, Real.sqrt_mul hab (c * d)]
    ring
  have hamgm : 2 * Real.sqrt (a * b * (c * d)) ≤ a * d + c * b := by
    have h1 : (0:ℝ) ≤ a * d := mul_nonneg ha hd
    have h2 : (0:ℝ) ≤ c * b := mul_nonneg hc hb
    have h3 : a * b * (c * d) = (a * d) * (c * b) := by ring
    rw [h3, Real.sqrt_mul h1 (c * b)]
    nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (c * b)),
      Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (c * b)]
  have hsq : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 ≤ (a + c) * (b + d) := by
    rw [hfirst]; nlinarith [hamgm]
  calc Real.sqrt (a * b) + Real.sqrt (c * d)
      = Real.sqrt ((Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((a + c) * (b + d)) := Real.sqrt_le_sqrt hsq

end

end Work.FTS.EllSol.Trunc
