/-
# `Work.FTS.EllSol.VthAuxC.identC` — the pointwise identity `∂_θ(Vop Ξ) = -(F + 6Ψ̂ + 6(-Ḡ sin2θ) + A + D)`

For `Ξ = PhiTil α g Φg = EllResid α g Φg` and `Ψ̂ = ellShift α g Φg` (so that `Ξ = Ψ̂ - Ḡ sin 2θ`),
the derivative of the coefficient `Vop Ξ = ∂_θΞ - tan θ · Ξ` along `θ` is

```
∂_θ(Vop Ξ) = -(orthSource g + 6Ψ̂ + 6(-Ḡ·sin 2θ) + α²z²∂_z²Ψ̂ + α(5+α)z∂_zΨ̂),
```

the crucial point being that **no `α^{-1}` survives** (the singular terms cancel, which is exactly
what the choice `G = G_* + Ḡ` of the paper's §"The singular term" is for).

Proof: `∂_θ(Vop U) = -(L₀U + 6U)` (`vthC_pth_Vop_eq`), `L₀Ξ = L₀Ψ̂` (linearity of `L₀`
+ `L₀(Ḡ sin 2θ) = 0`, `Work.Elliptic.Lzero_sin_two_mul`), and `L₀Ψ̂ = orthSource g + α²z²∂_z²Ψ̂ +
α(5+α)z∂_zΨ̂` (the equation `bslOp α Ψ̂ = orthSource g`, `EllWeakPos.eq`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.VthAuxC.helpersC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- On the open quadrant,
`∂_θ(Vop Ξ) = -(orthSource g + 6Ψ̂ + 6(-Ḡ·sin 2θ) + α²z²∂_z²Ψ̂ + α(5+α)(z∂_zΨ̂))`, where
`Ξ = PhiTil α g Φg` and `Ψ̂ = ellShift α g Φg`.  **No `α^{-1}` survives.** -/
theorem pth_Vop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ)
    (hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (ellShift α g Φg))
    (hGBsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) z θ
      = -(Work.Elliptic.orthSource g z θ + 6 * ellShift α g Φg z θ
          + 6 * (-(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ))
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
          + (α * (5 + α)) * Work.Spaces.Dz (ellShift α g Φg) z θ) := by
  have hSmW : Work.FTS.EllipticEst.SmoothOpen (ellShift α g Φg) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have hSmGBm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)) := by
    have h1 := Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hGBsm
    refine Work.FTS.EllipticEst.SmoothOpen.congr h1 (fun z θ _ _ _ => ?_)
    ring
  have hdec : (fun z θ => ellShift α g Φg z θ
      + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ))
      = Work.Construction.PhiTil α g Φg := by
    rw [Work.FTS.EllipticEst.PhiTil_eq_EllResid]
    exact (vthC_EllResid_eq_ellShift α g Φg).symm
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Φg) :=
    Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmW hSmGBm)
      (fun z θ _ _ _ => by rw [← hdec])
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have h1 : Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) z θ
      = -(Work.Elliptic.Lzero (Work.Construction.PhiTil α g Φg) z θ
          + 6 * Work.Construction.PhiTil α g Φg z θ) := by
    rw [Work.FTS.EllipticEst.Vop_eq α (Work.Construction.PhiTil α g Φg)]
    exact vthC_pth_Vop_eq hSmΞ hz hθ
  have h2 : Work.Elliptic.Lzero (Work.Construction.PhiTil α g Φg) z θ
      = Work.Elliptic.Lzero (ellShift α g Φg) z θ := by
    rw [← hdec, vthC_Lzero_add hSmW hSmGBm hz hθ,
      Work.Elliptic.Lzero_sin_two_mul (fun z => -(Work.Elliptic.Gbar α g z)) z θ hcos,
      add_zero]
  have h3 : Work.Elliptic.Lzero (ellShift α g Φg) z θ
      = Work.Elliptic.orthSource g z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (ellShift α g Φg) z θ)
        + (α * (5 + α)) * Work.Spaces.Dz (ellShift α g Φg) z θ := by
    have hb := Work.FTS.EllipticEst.TT.EllWeakPos.eq hweak z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    simp only [Work.Spaces.Dz]
    linarith [hb]
  rw [h1, h2, h3, ← hdec]
  ring

end Work.FTS.EllSol
