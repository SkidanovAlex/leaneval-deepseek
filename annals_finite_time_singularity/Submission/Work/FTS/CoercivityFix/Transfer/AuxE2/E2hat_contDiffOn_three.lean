/-
# `E2hat_contDiffOn_three` — the `C³`-regularity of the `D_z`-commutator defect

The defect `Ê₂ f = (2zf + 3z·D_θf)/(1+z)²` of `Work.FTS.CoercivityFix.Basic` is built from the
curried partials `f` and `D_θ f = sin(2θ)·∂_θ f`, so it is as smooth as `f` up to one angular
derivative.  A datum `f` in the localisation class `Work.FTS.LocData.SmoothQuad f` is genuinely
`C^∞` on `z > -1`, `0 < θ < π/2` (the order `Work.Stability.smoothOrder = ((⊤:ℕ∞):ℕ∞ω)`, *not*
the analytic order `⊤`), hence in particular on the smaller open quadrant
`Work.Construction.Qd = (0,∞) × (0,π/2)`, and the calculus of `Work.FTS.LocData.SmoothChain`
(`contDiffOn_Dth`, …) carries this to `D_θ f`; dividing by the nowhere-vanishing `(1+z)²` on
`z > 0` produces `Ê₂ f`, and the order is lowered from `smoothOrder` to `3`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

set_option autoImplicit false

/-- **`Ê₂ f` is `C³` on the open quadrant** for a datum which is `C^∞` on `z > -1`,
`0 < θ < π/2`.  The order `3` is what the transfer-coercivity induction consumes; the proof
actually produces any finite order (indeed `smoothOrder`), and `3` is obtained by `of_le`. -/
theorem E2hat_contDiffOn_three {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- `Qd = (0,∞) × (0,π/2)` sits inside the `SmoothQuad` half-strip `(-1,∞) × (0,π/2)`.
  have hsub : Work.Construction.Qd ⊆ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π/2) := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    exact ⟨by show (-1 : ℝ) < p.1; linarith, hp.2⟩
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.Construction.Qd := hsm.mono hsub
  have hDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hf
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.E2hat f)) Work.Construction.Qd := by
    have hfun : Function.uncurry (Work.FTS.CoercivityFix.E2hat f)
        = fun p : ℝ × ℝ =>
            (2 * p.1 * Function.uncurry f p
                + 3 * p.1 * Function.uncurry (Work.Spaces.Dth f) p) / (1 + p.1) ^ 2 := by
      funext p
      rcases p with ⟨z, θ⟩
      rfl
    rw [hfun]
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (((contDiffOn_const.mul contDiffOn_fst).mul hf).add
        ((contDiffOn_const.mul contDiffOn_fst).mul hDth))
    · exact (contDiffOn_const.add contDiffOn_fst).pow 2
    · intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      exact pow_ne_zero 2 (by linarith : (1 : ℝ) + p.1 ≠ 0)
  exact hmain.of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)

end Work.FTS.CoercivityFix.Transfer.AuxE2
