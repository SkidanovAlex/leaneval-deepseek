/-
# Sliding paraboloids: contact point conditions

Savin's Lemma 2.1 (`Small perturbation solutions for elliptic equations`, CPDE 32 (2007)): for a
solution `u` one slides the *concave* paraboloids `x ↦ -(a/2)‖x-y‖² + c` with vertex `y` in a set
`B` from below until first contact with the graph of `u`, and estimates the measure of the resulting
contact set.

This file contains the elementary consequences of the contact condition:
* `contact_hessian_lower`: at a contact point `x`, `D²u(x) ⪰ -a` (quadratic form sense);
* `contact_fderiv_eq`: at a contact point `x`, `Du(x) = -a(x - y)`, i.e. `y = x + a⁻¹ Du(x)`.
-/
import Mathlib
import Submission.Savin.Basic
import Submission.Commons.Analysis.Savin.fderiv_concave_paraboloid
import Submission.Commons.Analysis.Savin.hessian_concave_paraboloid
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_sub_of_mem_nhds

open Metric MeasureTheory Filter
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- First derivative of the concave paraboloid (bridge to the commons lemma). -/
theorem fderiv_parab (a c : ℝ) (y x : ℝ⁴) :
    fderiv ℝ (parab a y c) x = -(a • (innerSL ℝ (x - y))) := by
  unfold parab
  exact Commons.Analysis.Savin.fderiv_concave_paraboloid a c y x

/-- The second derivative of the concave paraboloid, on the diagonal. -/
theorem hessian_parab_diag (a c : ℝ) (y x v : ℝ⁴) :
    (fderiv ℝ (fderiv ℝ (parab a y c)) x) v v = -a * ‖v‖ ^ 2 := by
  unfold parab
  rw [Commons.Analysis.Savin.hessian_concave_paraboloid a c y x]
  simp only [neg_apply, smul_apply]
  rw [show ((innerSL ℝ) v) v = ‖v‖ ^ 2 by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]]
  ring

/-- **Contact point, second order condition.**  If `u` is `C²` at `x` and the concave paraboloid
`parab a y c` touches `u` from below at `x` (i.e. `u - parab a y c` has a local minimum at `x`),
then the Hessian of `u` at `x` dominates `-a` in the quadratic-form sense. -/
theorem contact_hessian_lower {u : ℝ⁴ → ℝ} {x : ℝ⁴} (hu : ContDiffAt ℝ 2 u x)
    {a c : ℝ} {y : ℝ⁴} (hmin : IsLocalMin (fun z => u z - parab a y c z) x) (v : ℝ⁴) :
    -a * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ u) x) v v := by
  have hpar : ContDiffAt ℝ 2 (parab a y c) x :=
    ((contDiff_parab a c y).contDiffAt).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have h1 : 0 ≤ (fderiv ℝ (fderiv ℝ (fun z => u z - parab a y c z)) x) v v :=
    fderiv_fderiv_nonneg_of_localMin (hu.sub hpar) hmin v
  have hsub : fderiv ℝ (fderiv ℝ (fun z => u z - parab a y c z)) x
      = fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ (parab a y c)) x := by
    have h := fderiv_fderiv_sub_of_contDiffAt (φ := u) (ψ := parab a y c) hu hpar
    rw [show (u - parab a y c) = (fun z => u z - parab a y c z) from rfl] at h
    exact h
  rw [hsub] at h1
  have h2 : ((fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ (parab a y c)) x) v) v
      = (fderiv ℝ (fderiv ℝ u) x) v v + a * ‖v‖ ^ 2 := by
    have hB : (fderiv ℝ (fderiv ℝ (parab a y c)) x) v v = -a * ‖v‖ ^ 2 :=
      hessian_parab_diag a c y x v
    simp only [sub_apply, hB]
    ring
  rw [h2] at h1
  linarith

/-- **Contact point, first order condition.**  If `u` is differentiable at `x` and the concave
paraboloid `parab a y c` touches `u` from below at `x`, then `Du(x) = -a (x - y)`, i.e. the vertex
of the paraboloid is `y = x + a⁻¹ Du(x)`. -/
theorem contact_fderiv_eq {u : ℝ⁴ → ℝ} {x : ℝ⁴} (hu : DifferentiableAt ℝ u x)
    {a c : ℝ} {y : ℝ⁴} (hmin : IsLocalMin (fun z => u z - parab a y c z) x) :
    fderiv ℝ u x = -(a • (innerSL ℝ (x - y))) := by
  have hpar : DifferentiableAt ℝ (parab a y c) x :=
    ((contDiff_parab a c y).differentiable (by simp)).differentiableAt
  have h0 : fderiv ℝ (fun z => u z - parab a y c z) x = 0 := hmin.fderiv_eq_zero
  rw [fderiv_fun_sub hu hpar] at h0
  have h1 : fderiv ℝ u x = fderiv ℝ (parab a y c) x := sub_eq_zero.mp h0
  rw [h1, fderiv_parab a c y x]

end Submission
