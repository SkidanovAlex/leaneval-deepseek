import Mathlib
import Submission.Work.EKLComp.BirkhoffDefs

namespace Work.EKLComp

/-- The Birkhoff average satisfies the shift identity relating the average of `f`
along the orbit of `T x` for `n` steps to the average along `x` for `n + 1` steps:
`n * birkA n (T x) = (n + 1) * birkA (n + 1) x - f x`. -/
theorem birkA_shift_mul {X : Type*} (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    (n : ℝ) * Work.EKLComp.Birkhoff.birkA T f n (T x) =
      ((n + 1 : ℕ) : ℝ) * Work.EKLComp.Birkhoff.birkA T f (n + 1) x - f x := by
  rcases n with _ | m
  · simp [Work.EKLComp.Birkhoff.birkA_def]
  · rw [Work.EKLComp.Birkhoff.birkA_def, Work.EKLComp.Birkhoff.birkA_def]
    have hL : (↑(Nat.succ m) : ℝ) *
        ((↑(Nat.succ m) : ℝ)⁻¹ * ∑ k ∈ Finset.range (Nat.succ m), f (T^[k] (T x)))
        = ∑ k ∈ Finset.range (Nat.succ m), f (T^[k] (T x)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (↑(Nat.succ m) : ℝ) ≠ 0), one_mul]
    have hR : (↑(Nat.succ m + 1) : ℝ) *
        ((↑(Nat.succ m + 1) : ℝ)⁻¹ * ∑ k ∈ Finset.range (Nat.succ m + 1), f (T^[k] x))
        = ∑ k ∈ Finset.range (Nat.succ m + 1), f (T^[k] x) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (↑(Nat.succ m + 1) : ℝ) ≠ 0), one_mul]
    rw [hL, hR]
    have h3 : ∑ k ∈ Finset.range (Nat.succ m), f (T^[k] (T x))
        = ∑ k ∈ Finset.range (Nat.succ m), f (T^[k + 1] x) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
    have h4 : ∑ k ∈ Finset.range (Nat.succ m + 1), f (T^[k] x)
        = (∑ k ∈ Finset.range (Nat.succ m), f (T^[k + 1] x)) + f x := by
      rw [Finset.sum_range_succ', Function.iterate_zero_apply]
    rw [h3, h4]
    ring

end Work.EKLComp
