import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real BigOperators Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol.TailBound

set_option autoImplicit false

theorem psiTrunc_tail (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∃ (C : ℝ) (b : ℕ → ℝ), 0 < C ∧ (∀ N : ℕ, 0 ≤ b N) ∧
      Filter.Tendsto b Filter.atTop (nhds 0) ∧
      ∀ (N M : ℕ) (z : ℝ), 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
        |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ| ≤ C * z ^ (-(1 / 2) : ℝ) * (b N + b M) := by
  sorry

end Work.FTS.H2.ModalSol.TailBound
