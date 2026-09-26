import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_countable

namespace Work.Smooth.Morse.Critical

/-- The Sard input, reduced to local finiteness of the critical values: a subset of `ℝ` whose
intersection with every closed bounded interval is finite is countable
(`countable_criticalValues_of_locallyFinite`), and a countable set of levels has measure zero
(`ae_regular_of_countable`). -/
theorem ae_regular_of_locallyFinite (ψ : Submission.Diffeo) (g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) (h : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) : Work.Smooth.Morse.AERegularValues ψ g :=
  ae_regular_of_countable ψ g
    (Work.Smooth.Morse.countable_criticalValues_of_locallyFinite ψ g h)

end Work.Smooth.Morse.Critical
