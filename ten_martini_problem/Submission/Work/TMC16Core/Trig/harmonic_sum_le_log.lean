import Mathlib

namespace Work.TMC16Core.Trig

section

set_option linter.unusedVariables false

/-- The `n`-th harmonic sum `∑_{k=1}^{n} 1/k` is at most `1 + log n`.

This is the classical upper bound for the harmonic numbers.  It follows directly
from Mathlib's `harmonic_le_one_add_log`, which states the corresponding bound
for the rational-valued harmonic number `harmonic n`
(`harmonic n = ∑_{i ∈ Icc 1 n} (i : ℚ)⁻¹`), after coercing to `ℝ`. -/
theorem harmonic_sum_le_log {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ ≤ 1 + Real.log (n : ℝ) := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  exact h

end

end Work.TMC16Core.Trig
