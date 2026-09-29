import Mathlib
import Submission.Work.Resample.auDefs

set_option linter.unusedVariables false

namespace Work.Resample

/-- `auM p α = (⌈√p⌉)·α` is at most `2p` as soon as `α² < p` (the truncation exponent is
within the window of the resampling word). -/
theorem auMBound (p α : ℕ) (hp : 100 ≤ p) (hαp : α ^ 2 < p) :
    Work.Resample.auM p α ≤ 2 * p := by
  have hα : α ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt]
    have := hαp
    rw [pow_two] at this
    omega
  have key : (Nat.sqrt p + 1) * Nat.sqrt p ≤ 2 * p := by
    have hs := Nat.sqrt_le p
    have hs2 := Nat.sqrt_le_self p
    nlinarith
  simp only [Work.Resample.auM]
  calc (Nat.sqrt p + 1) * α ≤ (Nat.sqrt p + 1) * Nat.sqrt p := Nat.mul_le_mul_left _ hα
    _ ≤ 2 * p := key

end Work.Resample
