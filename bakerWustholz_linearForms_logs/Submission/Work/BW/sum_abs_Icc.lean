import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The sum of `|s|` over the integer interval `[-S, S]` equals `S * (S + 1)`. -/
theorem sum_abs_Icc (S : ℕ) :
    ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), |s| = S * (S + 1) := by
  induction S with
  | zero => simp
  | succ S ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_Icc_succ_eq_add_endpoints (N := S)]
    rw [ih]
    have h1 : |(↑S + 1 : ℤ)| = ↑S + 1 := abs_of_nonneg (by positivity)
    have h2 : |(-(↑S + 1 : ℤ))| = ↑S + 1 := by rw [abs_neg, h1]
    rw [h1, h2]
    ring

end Work.BW
