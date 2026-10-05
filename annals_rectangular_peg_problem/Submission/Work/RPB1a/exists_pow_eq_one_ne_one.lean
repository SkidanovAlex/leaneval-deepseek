import Mathlib

namespace Work.RPB1a

/-- For every `k ≥ 2` there is a `k`-th root of unity different from `1`.
Given by the primitive `k`-th root `exp (2 * π * I / k)`. -/
theorem exists_pow_eq_one_ne_one (k : ℕ) (hk : 2 ≤ k) :
    ∃ ζ : ℂ, ζ ^ k = 1 ∧ ζ ≠ 1 := by
  have hk0 : k ≠ 0 := by omega
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / k), ?_, ?_⟩
  · exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  · exact (Complex.isPrimitiveRoot_exp k hk0).ne_one (by omega)

end Work.RPB1a
