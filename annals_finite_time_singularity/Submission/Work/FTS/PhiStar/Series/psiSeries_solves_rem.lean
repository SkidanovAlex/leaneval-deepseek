import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Psi23Smooth
import Submission.Work.FTS.PhiStar.telescoping
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.psiSeries_bslOp
import Submission.Work.FTS.PhiStar.Series.Conjunctions34
import Submission.Work.FTS.PhiStar.Series.Weil.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

theorem psiSeries_solves_rem :
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α
            (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
            z θ = Work.FTS.PhiStar.RemSource α ψ z θ) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z 0 = 0 ∧
        Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z (π / 2) = 0) ∧
    (∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto
          (fun z => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
          Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α ψ hα hα5 hψ
    exact Work.FTS.PhiStar.Series.Weil.smoothOpenR α ψ hα hα5 hψ
  · intro α ψ hα hα5 hψ
    exact psiSeries_bslOp α ψ hα hα5 hψ
  · intro α ψ hα hα5 hψ z
    exact psiSeries_dirichlet_inst α ψ z
  · intro α ψ hα hα5 hψ θ hθ
    exact psiSeries_tendsto_zero_inst α ψ hα hα5 hψ θ hθ

end Work.FTS.PhiStar.Series
