import Mathlib.NumberTheory.Harmonic.Int

namespace Commons.NumberTheory.Harmonic

theorem positive (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact_mod_cast le_of_lt (harmonic_pos hn)

end Commons.NumberTheory.Harmonic