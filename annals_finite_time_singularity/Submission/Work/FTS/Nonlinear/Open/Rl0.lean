/-
# Honest (open-quadrant) row — re-export

`Work.FTS.NonlinRows.Ctx` is verbatim the hypothesis bundle of the primed row statements, so a
row proved in the `NonlinRows` subproject is consumed here by `Ctx.mk'` (or directly, when the
source already uses the flat form).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.NAux3

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

theorem Rl0 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨_, h2, _⟩ := Work.FTS.NonlinRows.NAux3 IP hN hE
  obtain ⟨K, hK, h⟩ := h2
  exact ⟨K, hK, fun hα hα1 hαα₂ hg hs hell =>
    h (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs hell)⟩

end Work.FTS.Nonlinear.Open
