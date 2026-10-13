/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EllPkgClsVop` — the `V`-slot, and the `z`-differentiability of `L₁₂(F)`

`Vop Ψ = ∂_θΨ - tan θ·Ψ`, so for `(z,θ)` in the open quadrant

  `Vop (PhiTil α F Ψ) = Vop Ψ + (1/(4α)) · (tan θ sin 2θ - 2 cos 2θ) · L₁₂(F)(z)`

— an identity in which only *values* of `∂_θ` occur.  Consequently the smoothness of the `V`-slot
of the packages together with `SmoothOpen Ψ` forces `z ↦ L₁₂(F)(z)` to be differentiable on
`(0,∞)`, with the explicit identification at `θ = π/4`:
`L₁₂(F)(z) = 4α (Vop (PhiTil α F Ψ) z (π/4) - Vop Ψ z (π/4))`.

This is the missing input for the closure of `EllPkgCls` under differences: the `z`-derivative of
the `L₁₂`-part of `PhiTil` cannot be obtained from `SmoothOpen Ψ` alone (`L₁₂(F)` is an integral
of `F` over `(z,∞)`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The `θ`-derivative of `PhiTil`**: it splits unconditionally (the only `θ`-dependence of the
correction is the explicit factor `sin 2θ`). -/
theorem pth_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pth Ψ z θ
        - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) θ := by
  have hfun : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
      = fun θ' => Ψ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have hd2 : DifferentiableAt ℝ
      (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) θ := by
    fun_prop
  simp only [Work.Spaces.pth]
  rw [hfun]
  rw [show (fun θ' => Ψ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
      = (fun θ' => Ψ z θ')
        - (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) from rfl,
    deriv_sub (differentiableAt_tslice hΨ hz h0 h1) hd2]

/-- **The `z`-derivative of `PhiTil`**: it splits as soon as the `L₁₂`-part is differentiable. -/
theorem pz_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Work.Construction.L12 F z') z)
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
            * Work.Construction.L12 F z') z := by
  have hfun : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
      = fun z' => Ψ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z' := by
    funext z'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have hd2 : DifferentiableAt ℝ
      (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z') z := by
    refine (hu.const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z' => ?_))
    ring
  simp only [Work.Spaces.pz]
  rw [hfun]
  rw [show (fun z' => Ψ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z')
      = (fun z' => Ψ z' θ)
        - (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z') from rfl,
    deriv_sub (differentiableAt_zslice hΨ hz h0 h1) hd2]

/-- **The `V`-slot identifies the `L₁₂`-part of `PhiTil`.**  On the open quadrant,

  `Vop (PhiTil α F Ψ) = Vop Ψ + (1/(4α)) (tan θ · sin 2θ - 2 cos 2θ) · L₁₂(F)`.

Only the *values* of `∂_θ` occur, so this identity is unconditionally valid. -/
theorem Vop_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        + (1 / (4 * α)) * (Real.tan θ * Real.sin (2 * θ) - 2 * Real.cos (2 * θ))
            * Work.Construction.L12 F z := by
  have hpth := pth_PhiTil_eq (α := α) (F := F) (Ψ := Ψ) hΨ hz h0 h1
  have hval : Work.Construction.PhiTil α F Ψ z θ
      = Ψ z θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z := by
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  simp only [Work.Construction.Vop]
  rw [hpth, hval, deriv_const_sin_two_mul]
  ring

/-- **The `θ = π/4` identification of `L₁₂`.**  On `z > 0`,

  `L₁₂(F)(z) = 4α (Vop (PhiTil α F Ψ) z (π/4) - Vop Ψ z (π/4))`. -/
theorem L12_eq_of_Vop {α : ℝ} (hα : α ≠ 0) {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.L12 F z
      = (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
          - Work.Construction.Vop Ψ z (π / 4)) * (4 * α) := by
  have h := Vop_PhiTil_eq (α := α) (F := F) (Ψ := Ψ) hΨ (z := z) (θ := π / 4) hz
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsin : Real.sin (2 * (π / 4)) = 1 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]
  have hcos : Real.cos (2 * (π / 4)) = 0 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.cos_pi_div_two]
  rw [Real.tan_pi_div_four, hsin, hcos] at h
  norm_num at h
  have hcoef : α⁻¹ * (1 / 4) = 1 / (4 * α) := by ring
  rw [hcoef] at h
  have h4 : (4 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα
  have hmul : (1 / (4 * α)) * (4 * α) = 1 := by
    rw [one_div, inv_mul_cancel₀ h4]
  have hkey : (1 / (4 * α)) * Work.Construction.L12 F z
      = Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
        - Work.Construction.Vop Ψ z (π / 4) := by linarith [h]
  calc Work.Construction.L12 F z
      = ((1 / (4 * α)) * (4 * α)) * Work.Construction.L12 F z := by rw [hmul, one_mul]
    _ = ((1 / (4 * α)) * Work.Construction.L12 F z) * (4 * α) := by ring
    _ = (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
          - Work.Construction.Vop Ψ z (π / 4)) * (4 * α) := by rw [hkey]

/-- **`z ↦ L₁₂(F)(z)` is differentiable on `(0,∞)`** for the source `F` of a pair whose
`V`-slot is smooth on the open quadrant and whose stream function is `SmoothOpen`. -/
theorem differentiableAt_L12_of_Vop {α : ℝ} (hα : α ≠ 0) {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ)))
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z := by
  have hs1 : ContDiffOn ℝ 1
      (fun z' => Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z' (π / 4))
      (Set.Ioi 0) := contDiffOn_slice_pi_div_four (n := 1) (hV.forall 1)
  have hs2 : ContDiffOn ℝ 1 (fun z' => Work.Construction.Vop Ψ z' (π / 4)) (Set.Ioi 0) :=
    contDiffOn_slice_pi_div_four (n := 1) ((smoothOpen_Vop hΨ).forall 1)
  have hd : DifferentiableAt ℝ (fun z' =>
      Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z' (π / 4)
        - Work.Construction.Vop Ψ z' (π / 4)) z :=
    ((hs1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).sub
      ((hs2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz))
  refine (hd.mul_const (4 * α)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact L12_eq_of_Vop hα (F := F) (Ψ := Ψ) hΨ hz'

/-- The `z`-slices of `PhiTil α F Ψ` are differentiable on the open quadrant, whenever the
(possibly degenerate) part `(1/(4α)) L₁₂(F)` is. -/
theorem differentiableAt_zslice_PhiTil {α : ℝ} {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Work.Construction.L12 F z') z)
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α F Ψ z' θ) z := by
  have hfun : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
      = fun z' => Ψ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z' := by
    funext z'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  rw [hfun]
  refine (differentiableAt_zslice hΨ hz h0 h1).sub ?_
  refine (hu.const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun z' => ?_))
  ring

/-- The `θ`-slices of `PhiTil α F Ψ` are differentiable on the open quadrant (no hypothesis on
the `L₁₂`-part is needed). -/
theorem differentiableAt_tslice_PhiTil {α : ℝ} {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ)
    (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α F Ψ z θ') θ := by
  have hfun : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
      = fun θ' => Ψ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  rw [hfun]
  refine (differentiableAt_tslice hΨ hz h0 h1).sub ?_
  fun_prop

end Work.FTS.StrongEps.EComparison
