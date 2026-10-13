import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.Nonlinear.Open.Row14
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

theorem NRow14T2 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.VocabO2.Ctx2 α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2sg α Φs g) ∧
        |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  -- Row 14 (`N₂^{sg} = -2·𝒰(Φ̃_*)·∂_θ g`) is proved in full in the `StarPkgo2` vocabulary
  -- (`𝒰(Φ̃_*)/sin 2θ` priced by `StarPkgo2.UsW`), with the hypotheses of `Ctx2` unpacked.
  -- `Work.FTS.VocabO2.Ctx2` is exactly that conjunction, so the node is its `Ctx2`-wrapper.
  obtain ⟨K, hK, hrow⟩ := Work.FTS.Nonlinear.Open.Row14 IP hN hE
  refine ⟨K, hK, ?_⟩
  intro α g Φs Φg hctx
  unfold Work.FTS.VocabO2.Ctx2 at hctx
  rcases hctx with ⟨hα, hα1, hαα₂, hgal, hs2, hell⟩
  exact hrow hα hα1 hαα₂ hgal hs2 hell

end Work.FTS.NonlinRows
