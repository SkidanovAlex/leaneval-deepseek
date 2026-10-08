import Mathlib

namespace Work.BG

theorem units_sq_eq_one_eq_one_or_eq_neg_one (u : ℂˣ) (h : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h1 : (u : ℂ) ^ 2 = 1 := by
    have := congrArg (fun x : ℂˣ => (x : ℂ)) h
    simpa using this
  have h2 : ((u : ℂ) - 1) * ((u : ℂ) + 1) = 0 := by
    have : (u : ℂ) ^ 2 - 1 ^ 2 = 0 := by rw [h1]; ring
    rwa [sq_sub_sq, mul_comm] at this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; exact Units.ext (sub_eq_zero.mp h3)
  · right; exact Units.ext (add_eq_zero_iff_eq_neg.mp h3)

end Work.BG
