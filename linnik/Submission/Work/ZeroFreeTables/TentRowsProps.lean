import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentIf

namespace Work.ZeroFreeTables

theorem TentRowsProps (p : ℝ × ℝ × ℝ) (hp : p ∈ Work.ZeroFreeTables.tentRows) :
    p.1 ∈ ([6 / 5, 23 / 20, 11 / 10, 21 / 20, 1] : List ℝ) ∧ 0 < p.1 ∧ 0 ≤ p.2.1 ∧
      0 < p.2.2 ∧ Work.ZeroFreeTables.A₀ < p.1 / 2 := by
  simp only [Work.ZeroFreeTables.tentRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [List.mem_cons, Work.ZeroFreeTables.A₀]

end Work.ZeroFreeTables
