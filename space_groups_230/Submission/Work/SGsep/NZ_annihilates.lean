import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- `N_A (A - 1) = 0` and `(A - 1) N_A = 0` when `A` has finite order: `N_A A = ∑_{1 ≤ i ≤ m} A^i =
N_A` (telescoping, using `A^m = 1`). -/
theorem NZ_annihilates {A : IMat} (h : ∃ m : ℕ, 1 ≤ m ∧ A ^ m = 1) :
    NZ A * (A - 1) = 0 ∧ (A - 1) * NZ A = 0 := by
  obtain ⟨h1, h2⟩ := mOrd_spec h
  constructor
  · rw [NZ, Nsum, geom_sum_mul, h2, sub_self]
  · rw [NZ, Nsum, mul_geom_sum, h2, sub_self]

end Work.SGsep
