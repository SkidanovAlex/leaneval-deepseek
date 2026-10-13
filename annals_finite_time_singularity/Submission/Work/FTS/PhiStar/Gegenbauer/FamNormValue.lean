import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.FTS.PhiStar.Gegenbauer

/-- The set integral over `Work.Spaces.Iθ = Set.Icc 0 (π/2)` is the interval integral over
`0..π/2`.  (`0 ≤ π/2` so `intervalIntegral.integral_of_le` applies, and `Icc` and `Ioc` differ
only by the null set `{π/2}`.) -/
private lemma iotaInterval_eq (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]

theorem FamNormValue (m : ℕ) : (∫ θ in (0 : ℝ)..(π / 2), Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  have h := iotaInterval_eq (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  exact h.symm.trans (eFam_norm_fts m)

end Work.FTS.PhiStar.Gegenbauer
