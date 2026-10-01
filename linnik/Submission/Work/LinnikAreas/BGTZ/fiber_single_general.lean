import Mathlib

namespace Work.LinnikAreas.BGTZ

theorem fiber_single_general (t : Finset ℕ) (d n : ℕ) (hd : 1 ≤ d) (X : ℕ → ℝ) :
    (∑ r ∈ t, (if d * r = n then X r else 0))
      = (if d ∣ n ∧ n / d ∈ t then X (n / d) else 0) := by
  have hdpos : 0 < d := hd
  by_cases hdvd : d ∣ n
  · -- Unique solution `r = n / d` of `d * r = n`, and `d * (n / d) = n`.
    have key : ∀ r : ℕ, d * r = n ↔ r = n / d := by
      intro r
      constructor
      · intro h
        rw [← h, Nat.mul_div_cancel_left r hdpos]
      · intro h
        rw [h, Nat.mul_div_cancel' hdvd]
    have hsum : (∑ r ∈ t, (if d * r = n then X r else 0))
        = ∑ r ∈ t, (if r = n / d then X r else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [key r]
    rw [hsum, Finset.sum_ite_eq' t (n / d) X]
    simp [hdvd]
  · -- No `r` satisfies `d * r = n`, so both sides vanish.
    have key : ∀ r : ℕ, ¬ (d * r = n) := by
      intro r h
      exact hdvd ⟨r, h.symm⟩
    have hsum : (∑ r ∈ t, (if d * r = n then X r else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      simp [key r]
    rw [hsum]
    simp [hdvd]

end Work.LinnikAreas.BGTZ
