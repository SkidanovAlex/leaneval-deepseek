import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.Analysis.Asymptotics.dyadicAnnulusTail

open Filter

namespace Commons.Analysis.Asymptotics

theorem eventually_log_ge (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) := by
  exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (Filter.eventually_ge_atTop b)

end Commons.Analysis.Asymptotics