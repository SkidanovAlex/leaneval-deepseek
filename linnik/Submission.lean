import ChallengeDeps
import Submission.Work.LinnikFinal

open LeanEval.NumberTheory.Linnik

namespace Submission

/-!
# Linnik's theorem (exponent 5.5 = 11/2), after Heath-Brown (1992)

The theorem below is `Work.LinnikFinal.linnik_final`: the composition
(`Work.LinnikContract2.linnik_of_areas`) of the seven proved contract areas
(zero-free regions, zero-density estimates, the Deuring–Heilbronn repulsion and
the weighted prime sum of Heath-Brown §§13–15).
-/

/-- **Linnik's theorem with the explicit exponent 5.5** (Heath-Brown 1992):
for some absolute constant `c`, every reduced progression `a mod d` with
`0 < a < d` has its least prime `p a d ≤ c * d ^ (11/2)`. -/
theorem linnik : ∃ c : ℝ, ∀ ⦃a d : ℕ⦄,
    0 < a → a < d → a.Coprime d → p a d ≤ c * d ^ (5.5 : ℝ) :=
  Work.LinnikFinal.linnik_final

end Submission
