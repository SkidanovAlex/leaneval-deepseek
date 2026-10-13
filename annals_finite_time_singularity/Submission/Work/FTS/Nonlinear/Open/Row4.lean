/-
# Honest (open-quadrant) row — re-export from the `NonlinRows` subproject

`Work.FTS.NonlinRows.Ctx` is verbatim the flat hypothesis bundle of the primed row statements,
so a row proved there is consumed here by `Ctx.mk'`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

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

theorem Row4 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
      |IP α (Work.FTS.Nonlin.N04bF α g) g| ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
      := by
  obtain ⟨K, hK, h⟩ := Work.FTS.NonlinRows.row4 IP hN hE
  exact ⟨K, hK, fun hα hα1 hαα₂ hg hs hell =>
    h (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs hell)⟩

end Work.FTS.Nonlinear.Open
