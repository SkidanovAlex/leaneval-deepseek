import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegExportIface.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXDiag

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `Work.FTS_RegExport.RXDiag.closedFormOpen`

**The closed form of the transport coefficients `Vz7`, `cs7` on the open quadrant.**

`Vz7 = (1-μ) + L₁₂(F)·c2m + 2αG·V(Φ̃)` and `cs7 = (1+μ) - L₁₂(F)/αG + sin²θ·𝔽K(F) - 2·ℛ(Φ̃)`
are written with the `Θ`-part in closed form, so that they are continuous up to `θ = π/2`
(see the design notes of `RegExportIface/Defs`).  On the *open* quadrant, where the two
`Θ`-identities `2αG·V(Θ) = L₁₂(F)·c2m(θ)` and `-2·ℛ(Θ) = -L₁₂(F)/αG + sin²θ·𝔽K(F)` hold (the
second needs `z∂_zL₁₂(F) = -𝔽K(F)`, i.e. the density hypotheses `hint`, `hcont`), the `Θ`-parts
drop out and the coefficients reduce to their *literal* form `(1∓μ) ± 2αG·(V/R)(Φ)`.

The two ingredients are

* the closed forms of `V(Θ)`, `ℛ(Θ)` (`two_mul_Vop_Theta`, `neg_two_mul_Rop_Theta`), and
* the subtractivity of `V`, `ℛ` at a point where both slices (in `z` and in `θ`) of both data
  are differentiable (`Vop_sub_of_diffAt`, `Rop_sub_of_diffAt`) — the hypotheses `hdz`, `hdθ`
  of the statement.  (`Work.R1G6.annOp_sub` proves the sibling statement for *jointly*
  differentiable data.)
-/

/-! ## Subtracting the two partials slicewise -/

private theorem pz_sub_of_diffAt {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Spaces.pz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pz A z θ - Work.Spaces.pz B z θ := by
  simp only [Work.Spaces.pz]
  exact deriv_sub hA hB

private theorem pth_sub_of_diffAt {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Spaces.pth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pth A z θ - Work.Spaces.pth B z θ := by
  simp only [Work.Spaces.pth]
  exact deriv_sub hA hB

/-- `V` is subtractive at a point where both `θ`-slices are differentiable:
`V(A - B) = V(A) - V(B)`. -/
private theorem Vop_sub_of_diffAt {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Construction.Vop (fun z θ => A z θ - B z θ) z θ
      = Work.Construction.Vop A z θ - Work.Construction.Vop B z θ := by
  simp only [Work.Construction.Vop]
  rw [show Work.Spaces.pth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pth A z θ - Work.Spaces.pth B z θ from pth_sub_of_diffAt hA hB]
  ring

/-- `ℛ` is subtractive at a point where both slices (in `z` and in `θ`) are differentiable:
`ℛ(A - B) = ℛ(A) - ℛ(B)`. -/
private theorem Rop_sub_of_diffAt {α : ℝ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hAθ : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hBθ : DifferentiableAt ℝ (fun θ' => B z θ') θ)
    (hAz : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hBz : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Construction.Rop α (fun z θ => A z θ - B z θ) z θ
      = Work.Construction.Rop α A z θ - Work.Construction.Rop α B z θ := by
  simp only [Work.Construction.Rop]
  rw [show Work.Spaces.pz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pz A z θ - Work.Spaces.pz B z θ from pz_sub_of_diffAt hAz hBz,
    show Work.Spaces.pth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pth A z θ - Work.Spaces.pth B z θ from pth_sub_of_diffAt hAθ hBθ]
  ring

/-! ## The two closed forms of `Θ` -/

/-- `2αG·V(Θ αG F) = L₁₂(F)·c2m(θ)` on the open quadrant. -/
private theorem two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hα0 : αG ≠ 0 := ne_of_gt hαG
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    rw [Work.Construction.pth_Theta_eq (α := αG) hαG z θ]
    ring
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-- `-2·ℛ(Θ αG F) = -L₁₂(F)/αG + sin²θ·𝔽K(F)` on the open quadrant, from the density
hypotheses `hint`, `hcont` (which give `z∂_zL₁₂(F) = -𝔽K(F)`). -/
private theorem neg_two_mul_Rop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) :
    -2 * Work.Construction.Rop αG (Work.Construction.Theta αG F) z θ
      = -(Work.Construction.L12 F z) / αG + (Real.sin θ) ^ 2 * Work.Construction.FK F z := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : αG ≠ 0 := ne_of_gt hαG
  have hDz := Work.Construction.Dz_Theta_eq (α := αG) (z := z) (θ := θ) (F := F)
    hαG hint hcont hz
  have hzDz : z * Work.Spaces.pz (Work.Construction.Theta αG F) z θ
      = -(1 / (4 * αG)) * Work.Construction.s2 θ * Work.Construction.FK F z := by
    simpa only [Work.Spaces.Dz] using hDz
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    rw [Work.Construction.pth_Theta_eq (α := αG) hαG z θ]
    ring
  have hpz : Work.Spaces.pz (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * Real.sin (2 * θ) * (-Work.Construction.FK F z / z) := by
    have h2 : z * ((1 / (4 * αG)) * Real.sin (2 * θ) * (-Work.Construction.FK F z / z))
        = -(1 / (4 * αG)) * Work.Construction.s2 θ * Work.Construction.FK F z := by
      rw [Work.Construction.s2]
      field_simp
    exact mul_left_cancel₀ hz0 (by rw [hzDz, h2])
  simp only [Work.Construction.Rop, hpth, hpz, Work.Construction.Theta, Work.Construction.s2]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-! ## The main statement -/

theorem closedFormOpen {αG : ℝ} (hαG : 0 < αG) {μ : ℝ → ℝ} {G Φ : Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2)
    (hdθ : DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdz : DifferentiableAt ℝ (fun z' => slice Φ τ z' θ) z)
    (hint : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) z) :
    (Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
        = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ) ∧
      (Work.FTS.RegExportIface.cs7 αG μ G Φ z θ τ
        = (1 + μ τ) - 2 * Work.Construction.Rop αG (slice Φ τ) z θ) := by
  -- the singular part `Θ` of the slice of `Φ` is differentiable in both variables
  have hΘθ : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ') θ := by
    have hfun : (fun θ' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ')
        = fun θ' => ((1 / (4 * αG))
            * Work.Construction.L12 (Work.Construction.Ftau αG G τ) z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun]
    exact (differentiableAt_const _).mul
      ((Real.differentiableAt_sin).comp θ
        ((differentiableAt_id (x := θ)).const_mul (2 : ℝ)))
  have hΘz : DifferentiableAt ℝ
      (fun z' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z' θ) z := by
    have hder : HasDerivAt (fun z' => Work.Construction.L12 (Work.Construction.Ftau αG G τ) z')
        (-(Work.Construction.L12dens (Work.Construction.Ftau αG G τ) z)) z :=
      Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := Work.Construction.Ftau αG G τ)
        (a := 0) (ρ := z) hint hcont hz
    have hfun : (fun z' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z' θ)
        = fun z' => ((1 / (4 * αG)) * Work.Construction.s2 θ)
            * Work.Construction.L12 (Work.Construction.Ftau αG G τ) z' := by
      funext z'
      simp only [Work.Construction.Theta]
    rw [hfun]
    exact hder.differentiableAt.const_mul _
  -- subtractivity of `V` and `ℛ` at the point
  have hVsub : Work.Construction.Vop
        (fun z θ => slice Φ τ z θ
          - Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ) z θ
      = Work.Construction.Vop (slice Φ τ) z θ
        - Work.Construction.Vop
            (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ :=
    Vop_sub_of_diffAt hdθ hΘθ
  have hRsub : Work.Construction.Rop αG
        (fun z θ => slice Φ τ z θ
          - Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ) z θ
      = Work.Construction.Rop αG (slice Φ τ) z θ
        - Work.Construction.Rop αG
            (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ :=
    Rop_sub_of_diffAt hdθ hΘθ hdz hΘz
  -- the two closed forms of `Θ`
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG
    (F := Work.Construction.Ftau αG G τ) (z := z) (θ := θ) hθ hθ'
  have hRΘ := neg_two_mul_Rop_Theta (αG := αG) hαG
    (F := Work.Construction.Ftau αG G τ) (z := z) (θ := θ) hz hθ hθ' hint hcont
  constructor
  · simp only [Work.FTS.RegExportIface.Vz7, Work.FTS.RegExportIface.phiTil]
    rw [show Work.Construction.PhiTil αG (Work.Construction.Ftau αG G τ) (slice Φ τ)
        = fun z θ => slice Φ τ z θ
            - Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ from rfl]
    rw [hVsub]
    linear_combination -hVΘ
  · simp only [Work.FTS.RegExportIface.cs7, Work.FTS.RegExportIface.phiTil]
    rw [show Work.Construction.PhiTil αG (Work.Construction.Ftau αG G τ) (slice Φ τ)
        = fun z θ => slice Φ τ z θ
            - Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ from rfl]
    rw [hRsub]
    linear_combination -hRΘ

end Work.FTS_RegExport.RXDiag
