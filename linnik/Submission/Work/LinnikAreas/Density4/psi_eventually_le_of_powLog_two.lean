import Mathlib

namespace Work.LinnikAreas.Density4

lemma psi_eventually_le_of_powLog_two
    (h : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ x / (Real.log x) ^ (2 : ℝ)) :
    ∃ M : ℕ, 3 ≤ M ∧ ∀ N : ℕ, M ≤ N →
      Chebyshev.psi (N : ℝ) ≤ (N : ℝ) + (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := h
  refine ⟨max 3 ⌈x₀⌉₊, le_max_left 3 ⌈x₀⌉₊, ?_⟩
  intro N hN
  have hx : x₀ ≤ (N : ℝ) := by
    have h1 : x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
    have h2 : (⌈x₀⌉₊ : ℕ) ≤ N := le_trans (le_max_right 3 ⌈x₀⌉₊) hN
    have h3 : (⌈x₀⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hb := hx₀ (N : ℝ) hx
  have hle : Chebyshev.psi (N : ℝ) - (N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ) :=
    le_trans (le_abs_self _) hb
  linarith

end Work.LinnikAreas.Density4
