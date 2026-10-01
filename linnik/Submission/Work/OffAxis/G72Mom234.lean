import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Defs
import Submission.Work.OffAxis.G72MomentClosed

namespace Work.OffAxis

/-- The second, third and fourth moments of HB Lemma 7.2's weight `g72`.

These are the specialisations `m = 2, 3, 4` of the closed form
`G72MomentClosed`:
`∫₀² y^m g72(y) dy = (16·2^{m+1}/15)·(1/(m+1) - 5/(m+3) + 5/(m+4) - 1/(m+6))`,
which for `m = 2, 3, 4` evaluates to `16/45`, `64/189`, `64/175`. -/
theorem G72Mom234 :
    (∫ y in (0:ℝ)..2, y^2 * Work.ZeroFreeTables.g72 y) = 16/45 ∧
    (∫ y in (0:ℝ)..2, y^3 * Work.ZeroFreeTables.g72 y) = 64/189 ∧
    (∫ y in (0:ℝ)..2, y^4 * Work.ZeroFreeTables.g72 y) = 64/175 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [G72MomentClosed 2]; norm_num
  · rw [G72MomentClosed 3]; norm_num
  · rw [G72MomentClosed 4]; norm_num

end Work.OffAxis
