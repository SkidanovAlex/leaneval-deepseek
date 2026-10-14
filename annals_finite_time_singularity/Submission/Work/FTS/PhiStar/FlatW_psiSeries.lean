import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.RouteB.bslSolExists_psiSeries_of_node_hyp
import Submission.Work.FTS.PhiStar.Series.psiSeries_solves_rem
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.VocabO2
import Submission.Work.H2W.FstarDzIterFourPsiAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem FlatW_psiSeries : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ →
    Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z
        * (Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ
           / Work.Construction.s2 θ)) (C * α ^ 2) := by
  obtain ⟨C1, hC10, hF1⟩ := Work.FTS.PhiStar.FlatWAux.Fam1Bound
  obtain ⟨C2, hC20, hF2⟩ := Work.FTS.PhiStar.FlatWAux.Fam2Bound
  refine ⟨max C1 C2 + 1, by positivity, ?_⟩
  intro α ψ hα hα5 hang z θ hz hθ0 hθ2
  have hα2 : (0 : ℝ) ≤ α ^ 2 := pow_nonneg (le_of_lt hα) 2
  refine ⟨fun k hk => ?_, fun k i hki => ?_⟩
  · refine le_trans (hF1 α ψ hα hα5 hang z θ hz hθ0 hθ2 k hk) ?_
    exact mul_le_mul_of_nonneg_right (by linarith [le_max_left C1 C2]) hα2
  · refine le_trans (hF2 α ψ hα hα5 hang z θ hz hθ0 hθ2 k i hki) ?_
    exact mul_le_mul_of_nonneg_right (by linarith [le_max_right C1 C2]) hα2

end Work.FTS.PhiStar
