import Mathlib

namespace Work.WilC4.ErealArith

theorem deep_eq_le {β x b : ℝ} (hβ : β ≠ 0) :
    (∃ d : ℝ, (β + β) * d = x ∧ d ≤ b) ↔ x / (2 * β) ≤ b := by
  have h2 : (2 : ℝ) * β ≠ 0 := by positivity
  have hbb : β + β = 2 * β := by ring
  constructor
  · rintro ⟨d, hd, hle⟩
    have hx : x = (2 * β) * d := by rw [← hbb, hd]
    have hxd : x / (2 * β) = d := by rw [hx]; field_simp
    rw [hxd]; exact hle
  · intro h
    refine ⟨x / (2 * β), ?_, h⟩
    rw [hbb]
    field_simp

end Work.WilC4.ErealArith
