import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 10 (star half): `(z+1)/z · ℛ(Φ̃_*)` is `C^∞` on the open quadrant

This file proves `starH_smoothOpen`.  The statement is a *smoothness* statement only:

* `StarPkgo.smooth` gives `SmoothOpen Φs`, i.e. `C^∞` of `Φs` on the open quadrant
  `Q0 = (0,∞) × (0,π/2)`;
* `Θ_*(α) = Θ α (F_*)` is `sin(2θ)/(2(1+z))` there (`L₁₂(F_*) = 2α/(1+z)`), hence `C^∞`
  (`smoothOpen_Theta_Fstar`), so `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on `Q0`;
* `ℛ` is a rational expression in `Ψ`, `∂_zΨ`, `∂_θΨ`, `sin θ`, `cos θ` divided by
  `cos θ ≠ 0` on `Q0`, and `∂_z`, `∂_θ` preserve interior `C^∞` (`contDiffOn_pz`,
  `contDiffOn_pth`), so `ℛ(Φ̃_*)` is `C^∞` on `Q0` (`smoothOpen_Rop`);
* the radial factor `(z+1)/z` is `C^∞` on `Q0` because `z > 0` there.

Nothing here needs the `z = 0`-smoothness (`SmoothQuad`, `z > -1`) that the primed
interface does not provide — which is why the proof does not go through the delivered
`SmoothQuad`-level lemma `row10aux.Rop_PhiTs_smoothQuad`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false

/-! ## Closure of `SmoothOpen` under the pointwise algebra

(`Work.FTS.EllipticEst` only exposes the `SmoothQuad`-level algebra; these are the
`Q0`-analogues, obtained by the same one-line `ContDiffOn` arguments.) -/

/-- `SmoothOpen` is closed under addition. -/
theorem smoothOpen_add {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ + G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ + G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p + Function.uncurry G p := rfl
  rw [h]
  exact hF.add hG

/-- `SmoothOpen` is closed under subtraction. -/
theorem smoothOpen_sub {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ - G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ - G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ - G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p - Function.uncurry G p := rfl
  rw [h]
  exact hF.sub hG

/-- `SmoothOpen` is closed under products. -/
theorem smoothOpen_mul {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ * G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p * Function.uncurry G p := rfl
  rw [h]
  exact hF.mul hG

/-! ## The datum `Φ̃_* = Φ_s - Θ_*(α)` -/

/-- The `SmoothQuad`-smoothness of `Θ_*(α)` restricts to the open quadrant `Q0`. -/
theorem smoothOpen_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hquad : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.smoothQuad_Theta_Fstar hα hα1
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.quadU := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩
  exact hquad.mono hsub

/-- `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on the open quadrant as soon as `Φ_s` is. -/
theorem smoothOpen_PhiTs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_Theta_Fstar hα hα1
  have hsub := smoothOpen_sub hs.smooth hΘ
  show Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact hsub

/-! ## `ℛ` preserves `C^∞` on the open quadrant -/

/-- **`ℛ(Ψ)` is `C^∞` on the open quadrant when `Ψ` is.**  The only point to check is the
division by `cos θ`, legitimate because `cos θ > 0` for `θ ∈ (0, π/2)`; the two derivatives
`∂_zΨ`, `∂_θΨ` are `C^∞` there by `contDiffOn_pz`/`contDiffOn_pth`.  This is the
`SmoothOpen`-analogue of `row10aux.smoothQuad_Rop`. -/
theorem smoothOpen_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have hQ : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pz hQ hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth hQ hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-! ## The radial factor and the target -/

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant (its only singularity is at
`z = 0`, which is outside `Q0`). -/
theorem smoothOpen_zPlusOne_div_z :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)
      = fun p : ℝ × ℝ => (p.1 + 1) / p.1 := rfl
  rw [h]
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

theorem starH_smoothOpen :
    ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}, 0 < α → α ≤ 1 →
      Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  intro α Cs Φs hα hα1 hs
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    smoothOpen_PhiTs hα hα1 hs
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    smoothOpen_Rop hΦ
  exact smoothOpen_mul smoothOpen_zPlusOne_div_z hR

end Work.FTS.NonlinRows.NRow10aux
