import Mathlib

namespace Work.C17

theorem summable_shift_pow (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Summable (fun j : ℕ => ((N : ℝ) + 2 + j) * ρ ^ (2 * (N + 1 + j) - 1)) := by
  have hρ2 : ‖ρ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hρ0, hρ1]
  -- exponent identity
  have hexp : ∀ j : ℕ, ρ ^ (2 * (N + 1 + j) - 1)
      = ρ ^ (2 * N + 1) * (ρ ^ 2) ^ j := by
    intro j
    have h1 : 2 * (N + 1 + j) - 1 = 2 * N + 1 + 2 * j := by omega
    rw [h1, pow_add, pow_mul]
  have h1 : Summable (fun j : ℕ => (j : ℝ) * (ρ ^ 2) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ρ ^ 2) hρ2
  have h2 : Summable (fun j : ℕ => ((N : ℝ) + 2) * (ρ ^ 2) ^ j) :=
    (summable_geometric_of_norm_lt_one hρ2).mul_left _
  have h3 : Summable (fun j : ℕ => ((N : ℝ) + 2) * (ρ ^ 2) ^ j + (j : ℝ) * (ρ ^ 2) ^ j) :=
    h2.add h1
  have h4 : Summable
      (fun j : ℕ => ρ ^ (2 * N + 1) * (((N : ℝ) + 2) * (ρ ^ 2) ^ j + (j : ℝ) * (ρ ^ 2) ^ j)) :=
    h3.mul_left _
  refine h4.congr ?_
  intro j
  rw [hexp j]
  ring

end Work.C17
