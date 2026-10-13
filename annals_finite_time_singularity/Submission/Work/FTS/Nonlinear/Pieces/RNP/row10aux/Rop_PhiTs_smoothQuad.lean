import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_hLoc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SmoothQuad (ℛ(Φ̃_*))` for an `SmoothQuad` datum `Φ_s`

Row 10 of the design table needs the *coefficient* `ℛ(Φ̃_*)` of the nonlinear term `N₁^{*g}`
to be smooth on the open quadrant: this file supplies exactly that,
`Rop_PhiTs_smoothQuad`.

Two observations do the work, and both are elementary.

* `ℛ` is a rational expression in `Ψ`, `∂_zΨ`, `∂_θΨ` and `sin θ`, `cos θ`, divided by
  `cos θ`.  On the open quadrant `θ ∈ (0, π/2)` every one of those ingredients is `C^∞`
  (`Work.FTS.LocData.contDiffOn_pz`/`contDiffOn_pth` for the two derivatives, and
  `cos θ ≠ 0` for the division), so `ℛ` preserves `SmoothQuad`.

* `Φ̃_* = Φ_s - Θ_*(α)` with `Θ_*(α) = (1/(4α)) sin(2θ) L₁₂(F_*)(z)`.  The profile identity
  `L₁₂(F_*)(z) = 2α/(1+z)` (valid on the whole range `z > -1`, which is the range of
  `SmoothQuad`: `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`) turns `Θ_*(α)` into
  the completely explicit `sin(2θ)/(2(1+z))`, which is visibly `C^∞` on the open quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row10aux

set_option autoImplicit false

/-! ## `ℛ` preserves `SmoothQuad` -/

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there: on `quadU` the angle lies in
`(0, π/2)`, where `cos` is strictly positive.  All the remaining factors are the smooth
functions `sin θ`, `cos θ`, `z`, the datum `Ψ` itself, and its two first derivatives
(`contDiffOn_pz`, `contDiffOn_pth`). -/
theorem smoothQuad_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) := by
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.Spaces.quadU :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.Spaces.quadU :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Spaces.quadU :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.Spaces.quadU :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.Spaces.quadU :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.Spaces.quadU, Real.cos p.2 ≠ 0 := by
    intro p hp
    have hpos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(Set.mem_Ioo.mp hp.2).1, Real.pi_pos], (Set.mem_Ioo.mp hp.2).2⟩
    exact ne_of_gt hpos
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-! ## The singular part `Θ_*(α) = Θ α (F_*)` of `Φ̃_*` -/

/-- **`Θ_*(α)` is `C^∞` on the open quadrant.**  By the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for every `z > -1`) it is the explicit function
`(z, θ) ↦ sin(2θ)/(2(1+z))`, which is smooth there because the denominator `2(1+z)` is
positive. -/
theorem smoothQuad_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1; linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-! ## The target -/

/-- **Row 10 (smoothness half).**  If the stream function `Φ_s` of the profile is `C^∞` on the
open quadrant then so is the coefficient `ℛ(Φ̃_*) = ℛ(Φ_s - Θ_*(α))` of the nonlinear term
`N₁^{*g} = 2ℛ(Φ̃_*)·g`.  This is `smoothQuad_Rop` applied to
`Φ̃_* = Φ_s - Θ_*(α)`, `smoothQuad_sub` of the hypothesis and `smoothQuad_Theta_Fstar`. -/
theorem Rop_PhiTs_smoothQuad {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.LocData.SmoothQuad Φs) :
    Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
  have hTheta : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothQuad_Theta_Fstar hα hα1
  have hPhi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
    show Work.FTS.LocData.SmoothQuad
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact Work.FTS.LocData.smoothQuad_sub hs hTheta
  exact smoothQuad_Rop hPhi

end Work.FTS.Nonlinear.Pieces.RNP.row10aux
