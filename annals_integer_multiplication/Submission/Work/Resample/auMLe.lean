import Mathlib
import Submission.Work.Resample.auDefs

namespace Work.Resample

theorem auMLe (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) :
    Work.Resample.auM p α ≤ 2 * p ∧ Work.Resample.auL p α ≤ 4 * p + 1 := by
  have hαle : α ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt]
    calc α * α = α ^ 2 := by ring
      _ ≤ p := le_of_lt hαp
  have hM : auM p α ≤ 2 * p := by
    simp only [auM]
    calc (Nat.sqrt p + 1) * α
        ≤ (Nat.sqrt p + 1) * Nat.sqrt p := Nat.mul_le_mul_left _ hαle
      _ = Nat.sqrt p * Nat.sqrt p + Nat.sqrt p := by ring
      _ ≤ p + p := by
          have h1 := Nat.sqrt_le p
          have h2 := Nat.sqrt_le_self p
          omega
      _ = 2 * p := by ring
  constructor
  · exact hM
  · simp only [auL]
    omega

end Work.Resample
