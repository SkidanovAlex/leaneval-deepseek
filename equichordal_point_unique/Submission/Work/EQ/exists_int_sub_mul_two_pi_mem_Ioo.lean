import Mathlib

namespace Work.EQ

/-- If `sin ψ > 0`, then `ψ` is congruent modulo `2π` to a number in `(0, π)`:
subtract the largest integer multiple of `2π` not exceeding `ψ`. -/
theorem exists_int_sub_mul_two_pi_mem_Ioo {ψ : ℝ} (hψ : 0 < Real.sin ψ) :
    ∃ k : ℤ, 0 < ψ - k * (2 * Real.pi) ∧ ψ - k * (2 * Real.pi) < Real.pi := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊ψ / (2 * Real.pi)⌋ with hk
  set x : ℝ := ψ - k * (2 * Real.pi) with hx
  have hxdef : x = ψ - k * (2 * Real.pi) := hx
  have hnn : 0 ≤ x := by
    rw [hxdef, hk]; exact Int.sub_floor_div_mul_nonneg ψ h2pi
  have hlt : x < 2 * Real.pi := by
    rw [hxdef, hk]; exact Int.sub_floor_div_mul_lt ψ h2pi
  have hsin : Real.sin x = Real.sin ψ := by
    rw [hxdef]; exact Real.sin_sub_int_mul_two_pi ψ k
  have hpos : 0 < x := by
    refine lt_of_le_of_ne hnn ?_
    intro hx0
    have hz : Real.sin x = 0 := by rw [← hx0, Real.sin_zero]
    rw [hsin] at hz
    linarith
  refine ⟨k, ?_, ?_⟩
  · rw [← hxdef]; exact hpos
  · rw [← hxdef]
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : 0 ≤ x - Real.pi := by linarith
    have h2 : x - Real.pi ≤ Real.pi := by linarith
    have h3 : 0 ≤ Real.sin (x - Real.pi) := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
    have h4 : Real.sin (x - Real.pi) = - Real.sin x := Real.sin_sub_pi x
    rw [hsin] at h4
    linarith

end Work.EQ
