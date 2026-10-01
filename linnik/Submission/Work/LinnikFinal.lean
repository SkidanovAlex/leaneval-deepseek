import Submission.Work.LinnikContract2.Compose
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikContract2.CarryOver
import Submission.Work.LinnikContract2.A7.Area7Final
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas.area2
import Submission.Work.LinnikAreas.area6
import Submission.Work.LinnikAreas2.area4_r2
import Submission.Work.ZeroFreeTables.Main

/-!
# Linnik's theorem with exponent 5.5: final assembly

The seven contract areas, composed by `Work.LinnikContract2.linnik_of_areas`.
-/

open LeanEval.NumberTheory.Linnik

namespace Work.LinnikFinal

/-- **Linnik's theorem with exponent `5.5`**: the least prime `p a d` of every reduced
progression `a mod d` with `0 < a < d` satisfies `p a d ≤ c * d ^ 5.5`. -/
theorem linnik_final : ∃ c : ℝ, ∀ ⦃a d : ℕ⦄,
    0 < a → a < d → a.Coprime d → p a d ≤ c * d ^ (5.5 : ℝ) :=
  Work.LinnikContract2.linnik_of_areas
    (Work.LinnikContract2.area1_round1 Work.LinnikAreas.area1)
    (Work.LinnikContract2.area2_round1 Work.LinnikAreas.area2)
    Work.ZeroFreeTables.linnikContract2_Area3_of_engine
    Work.LinnikAreas2.area4_r2
    Work.LinnikContract2.area5
    (Work.LinnikContract2.area6_round1 Work.LinnikAreas.area6)
    Work.LinnikContract2.area7

end Work.LinnikFinal
