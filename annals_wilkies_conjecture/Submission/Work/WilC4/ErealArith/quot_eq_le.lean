import Mathlib

namespace Work.WilC4.ErealArith

theorem quot_eq_le {β x t : ℝ} (hβ : β ≠ 0) :
    (∃ e : ℝ, β * e = x ∧ e ≤ t) ↔ x / β ≤ t := by
  constructor
  · rintro ⟨e, he, het⟩
    rw [← he, mul_div_cancel_left₀ _ hβ]
    exact het
  · intro h
    exact ⟨x / β, by rw [mul_div_cancel₀ _ hβ], h⟩

end Work.WilC4.ErealArith
