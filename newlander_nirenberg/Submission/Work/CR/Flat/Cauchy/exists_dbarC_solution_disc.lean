import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.dbarC_cauchyTransform
import Submission.Work.CR.Flat.Cauchy.holderNorm_one_cauchyTransform_le

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- **The one-variable `∂̄`-Poincaré result on a disc, with estimates** (the `n = 1`
case of the flat `∂̄`-Poincaré problem).  For `0 < α < 1` there is a constant
`C = C(ρ,α)` such that for every `C¹` function `f` supported in the disc of
radius `ρ/2` the Cauchy potential `u = cauchyTransform ρ f` satisfies

* `∂̄u = f` on the disc of radius `ρ/2` (a *solution* of the `∂̄`-equation), and
* `‖u‖_{C^{1,α}} ≤ C ‖f‖_{C^{0,α}(ℂ)}` — a gain of exactly one derivative, on the
  slightly smaller disc, with a uniform constant.

This is what a caller iterating the Newlander–Nirenberg perturbation can use
directly.  It follows from `dbarC_cauchyTransform` (the equation) and
`holderNorm_one_cauchyTransform_le` (the Schauder estimate). -/
theorem exists_dbarC_solution_disc {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → SupportedInBall (ρ / 2) f →
      (∀ z : ℂ, ‖z‖ < ρ / 2 → dbarC (cauchyTransform ρ f) z = f z) ∧
      holderNorm 1 α (cauchyTransform ρ f) (Metric.ball 0 (ρ / 2))
        ≤ ENNReal.ofReal C * holderNorm 0 α f Set.univ := by
  obtain ⟨C, hCpos, hC⟩ := holderNorm_one_cauchyTransform_le (ρ := ρ) (α := α) hρ hα hα1
  exact ⟨C, hCpos, fun f hf hfsupp =>
    ⟨fun z hz => dbarC_cauchyTransform hρ hf hfsupp hz, hC f hf hfsupp⟩⟩

end Work.CR.Flat.Cauchy
