/-
# Row 11 of the N4 table: the smoothness half — `N₁^{**} = 2 ℛ(Φ̃_*) F_*` is `C^∞`

The piece of row 11 is `N₁^{**} = 2 ℛ(Φ̃_*) F_*` (`Work.FTS.Nonlin.N1ss`).  The design's route
(`FTS/N45_DESIGN_LEAD.md` §3.4, row 11) is

  `WtoH` (`|f|_{ℋ⁴} ≤ C·|((z+1)³/z²) f|_{𝒲^{4,∞}}`), applied to `f = N₁^{**}`, followed by a
  product rule in the `𝒲^{4,∞}`-norm for the *weighted* coefficient
  `ℛ̃(Φ̃_*) = ((z+1)/z)·ℛ(Φ̃_*)`.

Before any of that one needs the hypothesis of `WtoH`, namely that the function is smooth on
the open quadrant — this module supplies exactly that:

  `SmoothQuad (N₁^{**})`,  from `StarPkg α Cs Φs`.

The argument is the same one that row 10 uses for `N₁^{*g} = 2ℛ(Φ̃_*)·g` (the sibling file
`Submission/Work/FTS/Nonlinear/Pieces/RNP/row10aux/Rop_PhiTs_smoothQuad.lean`):

* `Φ̃_* = Φ_s - Θ_*(α)` with `Θ_*(α) = (1/(4α)) sin(2θ) L₁₂(F_*)`; the profile identity
  `L₁₂(F_*)(z) = 2α/(1+z)` on the whole range `z > -1` turns `Θ_*(α)` into the explicit
  `sin(2θ)/(2(1+z))`, so `Θ_*(α)` — and hence `Φ̃_*`, by `StarPkg.smooth` — is `C^∞` on the
  open quadrant;
* `ℛ` is a rational expression in `Ψ`, `∂_zΨ`, `∂_θΨ`, `sin θ`, `cos θ`, divided by `cos θ`,
  which is legitimate on the quadrant (`cos θ > 0` there);
* `F_*` is `C^∞` on the quadrant, and `SmoothQuad` is closed under products and constant
  multiples.

The two auxiliary lemmas `smoothQuad_Rop` and `smoothQuad_Theta_Fstar` are proved here (they
are the two ingredients of the sibling row-10 module) so that this file depends only on the
`LocData` smooth-calculus, and not on the whole row-10 import cone.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

/-! ## The two ingredients: `ℛ` preserves `C^∞`, and `Θ α (F_*)` is `C^∞` -/

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there: on `quadU = (z > -1) × (0 < θ < π/2)`
the angle lies in `(0, π/2)`, where `cos` is strictly positive.  All the remaining factors are
the smooth functions `sin θ`, `cos θ`, `z`, the datum `Ψ` itself, and its two first derivatives
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

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant.**  By the profile identity
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

/-- **Row 11 (smoothness half).**  `N₁^{**} = 2 ℛ(Φ̃_*) F_*` is `C^∞` on the open quadrant
whenever the N3 package `StarPkg α Cs Φs` holds — the only field of the package that is used
is `StarPkg.smooth` (`SmoothQuad Φ_s`); the constant `Cs` enters only through the elliptic data
of `Φ_s`.

The three factors are smooth on `quadU = (z > -1) × (0 < θ < π/2)`: `ℛ(Φ̃_*)` by
`smoothQuad_Rop` applied to `Φ̃_* = Φ_s - Θ_*(α)`, and `F_*` by `SmoothQuad_Fstar`. -/
theorem N1ss_smoothQuad {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1ss α Φs) := by
  -- `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞`
  have hTheta : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothQuad_Theta_Fstar hα hα1
  have hPhi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
    show Work.FTS.LocData.SmoothQuad
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact Work.FTS.LocData.smoothQuad_sub h.smooth hTheta
  -- the coefficient `ℛ(Φ̃_*)` is `C^∞`
  have hR : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    smoothQuad_Rop hPhi
  -- the profile `F_*` is `C^∞`
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.SmoothQuad_Fstar α
  -- the constant `2` and the product
  have h2R : Work.FTS.LocData.SmoothQuad
      (fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 hR
  have hprod : Work.FTS.LocData.SmoothQuad
      (fun z θ => (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * Work.Construction.Fstar α z θ) :=
    Work.FTS.LocData.smoothQuad_mul h2R hF
  -- `N₁^{**} = 2 ℛ(Φ̃_*) F_*` by definition (`N1ss` unfolds to the lambda of `hprod`)
  exact hprod

end Work.FTS.Nonlinear.Pieces.RNP
