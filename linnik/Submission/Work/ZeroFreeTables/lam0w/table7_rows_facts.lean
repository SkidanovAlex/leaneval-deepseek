import Mathlib
import Submission.Work.ZeroFreeTables.HBProps

namespace Work.ZeroFreeTables.lam0w

/-- Every row of HB Table 7 (as a pair of reals) lies in the box
`[0, 745/1000] × (0, 276/100]` and is ordered `λ₁ ≤ λ₂`; moreover any row whose
`λ₂`-entry exceeds `2.293` has `λ₁ ≤ 0.14`.  All of this is a finite check on the
seventeen transcribed rows. -/
theorem table7_rows_facts :
    (∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
      (0 : ℝ) ≤ p.1 ∧ p.1 ≤ 745 / 1000 ∧ 0 < p.2 ∧ p.2 ≤ 276 / 100 ∧ p.1 ≤ p.2) ∧
    (∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
      2293 / 1000 < p.2 → p.1 ≤ 14 / 100) := by
  constructor
  · intro p hp
    simp only [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable7, List.map_cons,
      List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num
  · intro p hp h
    simp only [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable7, List.map_cons,
      List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (try norm_num at h) <;> norm_num

end Work.ZeroFreeTables.lam0w
