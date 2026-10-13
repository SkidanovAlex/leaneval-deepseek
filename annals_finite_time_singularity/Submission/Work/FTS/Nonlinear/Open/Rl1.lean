/-
# `rl1` of the honest (open-quadrant) chapter — from `NonlinRows.rl1`

`rl1` is the zero-mode estimate `|L₁₂(N)(0)| ≤ K(α² + √α·X + α^{-3/2}X²)` (design L-N4.6, the
`N`-part).  It is proved in the `NonlinRows` subproject
(`Work.FTS.NonlinRows.rl1`, `sorry`-free) against the context `Work.FTS.NonlinRows.Ctx`, which is
verbatim the flat hypothesis bundle used by every row of this chapter; the re-export here only
unfolds it.  Unlike rows 10/11/14/15/18/19 it consumes no `𝒲^{4,∞}`-priced star field, so it is
stated with `VocabO.StarPkgo` (like its siblings `Rl0`/`Rl2`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.rl1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem Rl1 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨K, hK, h⟩ := Work.FTS.NonlinRows.rl1 IP hN hE
  exact ⟨K, hK, fun hα hα1 hαα₂ hg hs hell =>
    h (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs hell)⟩

end Work.FTS.Nonlinear.Open
