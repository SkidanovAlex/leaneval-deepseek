/-
# `Work.FTS_RegExport.RXR7.Support.FstarPartCont`

Joint continuity of the pair `(∂_z F_*, ∂_θ F_*)` of the reference profile

  `F_*(z,θ) = β (Γ(θ)/c(β)) · 2z/(1+z)²`,   `β = pExp α = 3α`,

on the open quadrant `(0,∞) × (0,π/2)`.

The two partials are *themselves* `C^∞` there: `F_*` is the product of the angular factor
`β · Γ(θ)/c(β)` — where `Γ(θ) = (sin θ cos²θ)^{β/3}` is `C^∞` on `(0,π/2)` because the base
`sin θ cos²θ` is strictly positive (and the real power is differentiable at every positive
base, with *no* sign condition on the exponent, so no hypothesis on `α` is needed) — with the
radial profile `2z/(1+z)²`, which is rational with its only pole at `z = -1`, i.e. `C^∞` on
`(0,∞)`.  Nothing more than the `C^∞`-calculus on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen.pz`, `.pth`, which come from the generic
`Work.FTS.LocData.contDiffOn_pz`, `contDiffOn_pth`) is required.

The auxiliary lemma `contDiffOn_uncurry_Fstar_Q0` keeps the exponent `β` general (the
existing `Work.FTS_RegExport.RXT.contDiffOn_Fstar_Q0` demands `0 < β ≤ 1`, which this
statement — with its *arbitrary* real `α` — cannot supply); the division by `c β` is handled
by `ContDiffOn.div_const`, which needs no non-vanishing hypothesis (`c β = 0` makes `F_*`
identically zero, still `C^∞`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7.Support

set_option autoImplicit false

/-- `F_*(·,·) = β·(Γ(θ)/c(β))·(2z/(1+z)²)` is `C^n` on the open quadrant `Q0`, for **every**
real exponent `β` (no sign hypothesis: on `Q0` the base `sin θ cos²θ` of the real power is
strictly positive, and division by `c β` is harmless since `c β = 0` only makes `F_*` vanish). -/
theorem contDiffOn_uncurry_Fstar_Q0 (β : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar β)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.contDiffOn_Gam_Q0 β n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2 / Work.Spaces.c β)
      Work.FTS.EllipticEst.Q0 := hGam.div_const _
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => β * (Work.Spaces.Gam β p.2 / Work.Spaces.c β))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_fst_of (Work.FTS_RegExport.RXT.contDiffOn_FM_Fstar n)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-- The reference profile `F_* = β(Γ/c)·F_{*,rad}` is `C^∞` on the open quadrant, for every
real `β`. -/
theorem smoothOpen_Fstar (β : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar β) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (contDiffOn_uncurry_Fstar_Q0 β)

/-- **Joint continuity of `(∂_zF_*, ∂_θF_*)` on the open quadrant.**  Each component is
`C^∞` there (`smoothOpen_Fstar` + `SmoothOpen.pz` / `SmoothOpen.pth`), hence continuous. -/
theorem FstarPartCont {α : ℝ} :
    ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) :=
    smoothOpen_Fstar (Work.FTS.Regularity.pExp α)
  have h1 : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pz
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) q.1 q.2)
      Work.FTS.EllipticEst.Q0 := hso.pz.continuousOn
  have h2 : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) q.1 q.2)
      Work.FTS.EllipticEst.Q0 := hso.pth.continuousOn
  exact h1.prodMk h2

end Work.FTS_RegExport.RXR7.Support
