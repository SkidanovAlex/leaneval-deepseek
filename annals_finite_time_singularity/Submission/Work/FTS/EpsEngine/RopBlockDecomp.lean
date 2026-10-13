/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/RopBlockDecomp.lean` — the `Rop` block's decomposition

`PhiTil α F Φ = Φ - Theta α F` is *affine in* `Φ`, and `Rop` is *linear in* its argument; hence

    PhiTil α f (Φs + E f) = PhiTil α f (E f) + PhiTil α F_* Φs + Theta α F_*,

so the `Rop` slot of `EpsDecay` splits into the three pieces bounded in
`Work.FTS.EpsEngine.ell_Rop_le` (`EllPkgGo`), `Work.FTS.EpsEngine.star_Rop_le` (`StarPkgo2`) and
`Work.FTS.EpsEngine.Theta_Fstar_ops` (explicit).  This module records the identity at a point where
the relevant `z`- and `θ`-slices are differentiable — the hypotheses of
`Work.FTS.EpsEngine.Rop_Uop_Vop_add`, applied twice.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EpsEngine.Rop_Uop_Vop_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The `Rop` slot's decomposition into its three pieces.** -/
theorem Rop_block_decomp {α : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Φs z' θ) z)
    (hz₃ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z' θ) z)
    (hz₄ : DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hθ₃ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z θ') θ)
    (hθ₄ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z θ') θ) :
    Work.Construction.Rop α (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
  -- the two function identities
  have hfun₁ : Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)
      = fun z θ => Work.Construction.PhiTil α f (E f) z θ + Φs z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hfun₂ : Φs = fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      + Work.Construction.Theta α (Work.Construction.Fstar α) z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  rw [hfun₁]
  have h₁ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).1
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).1
  have hRΦ : Work.Construction.Rop α Φs z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hRΦ]
  ring

end Work.FTS.EpsEngine
