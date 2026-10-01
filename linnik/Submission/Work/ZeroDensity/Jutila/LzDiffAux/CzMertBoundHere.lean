import Mathlib
import Submission.Work.ZeroDensity.Jutila.MertensMuDecay
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux

/-! The Mertens decay in the `czEps` envelope form used by the `cz` analysis. -/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-- `|Σ_{t ≤ T} μ(t)| ≤ CM·T·czEps cM T` for `T ≥ 1`, in the envelope notation of `CzRIAux`. -/
theorem CzMertBoundHere : ∃ CM cM : ℝ, 0 < CM ∧ 0 < cM ∧
    ∀ T : ℕ, 1 ≤ T → |czMert T| ≤ CM * (T : ℝ) * czEps cM (T : ℝ) := by
  obtain ⟨C, c, hC, hc, hM⟩ := Work.ZeroDensity.Jutila.MertensMuDecay
  refine ⟨C, c, hC, hc, fun T hT => ?_⟩
  have h := hM T hT
  unfold czMert czEps
  simpa using h

end

end Work.ZeroDensity.Jutila.LzDiffAux
