import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

/-!
# Regularity of the coefficient fields `ℛ(Ψ)`, `𝒱(Ψ)`, `𝒰(Ψ)`, `𝒰(Ψ)/sin 2θ`

The fields of the self-similar vorticity equation (`Work.Construction.Rop`, `.Vop`, `.Uop`) are
rational expressions in `Ψ`, `∂_zΨ`, `∂_θΨ` and the angular functions `sin θ`, `cos θ`,
`tan θ`; on the open quadrant `Q0 = (0,∞) × (0,π/2)` all of these are `C^∞` whenever `Ψ` is,
and the two denominators that appear (`cos θ` in `ℛ`, `sin 2θ` in `𝒰/sin 2θ`) do not vanish
there.  Together with the radial factor `(z+1)/z` (whose only singularity `z = 0` lies outside
`Q0`), this gives `Work.FTS.EllipticEst.SmoothOpen` of all six fields, plus the angular
derivative `∂_θ 𝒰(Ψ)`.

All inputs are already-delivered, `sorry`-free facts:

* `Work.FTS.NonlinRows.smoothOpen_Rop` (`ℛ` preserves `SmoothOpen`),
* `Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open`, `…smoothOpen_Vop_open` (`𝒰`, `𝒱` preserve
  `SmoothOpen`),
* `Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul`,
  `Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z`,
* `Work.FTS.EllipticEst.SmoothOpen.pth` (the angular derivative preserves `SmoothOpen`),
* the local lemma `smoothOpen_div_sin2` below (division by `sin 2θ` preserves `SmoothOpen`).
-/

/-- Division by `sin 2θ` preserves `C^∞` on the open quadrant (`sin 2θ > 0` for
`0 < θ < π/2`).  Copy of `Work.Blocks.smoothOpen_div_sin2`, kept local so that this module
depends only on the two smoothness-API imports. -/
theorem smoothOpen_div_sin2 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Real.sin (2 * θ)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

theorem FieldRegularity (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Rop α Ψ z θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Vop Ψ z θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ)) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Construction.Uop α Ψ)) := by
  have hR : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hsm
  have hV : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hsm
  have hU : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open hsm
  have hfac : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
  have hdiv : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) := by
    simpa only [Work.Construction.s2] using
      smoothOpen_div_sin2 (f := Work.Construction.Uop α Ψ) hU
  exact ⟨Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hR, hV,
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hV, hdiv,
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hdiv, hU.pth⟩

end Work.FTS.PhiStar.StarPkgo2Aux
