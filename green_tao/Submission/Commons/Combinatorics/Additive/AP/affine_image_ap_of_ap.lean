import Mathlib

namespace Commons.Combinatorics.Additive.AP

/-- If the set `{n | c * n + d ∈ A}` (i.e. the affine preimage of `A` under
`n ↦ c * n + d`, with `1 ≤ c`) contains arbitrarily long arithmetic
progressions, then so does `A` itself.

An AP `a + b * j` (for `j < k`) whose members all satisfy
`c * (a + b * j) + d ∈ A` is mapped by the affine function
`x ↦ c * x + d` to the AP `(c * a + d) + (c * b) * j` inside `A`, and
`1 ≤ c * b` since `1 ≤ c` and `1 ≤ b`. -/
theorem affine_image_ap_of_ap {A : Set ℕ} {c d : ℕ} (hc : 1 ≤ c)
    (hA : ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → c * (a + b * j) + d ∈ A) :
    ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A := by
  intro k
  obtain ⟨a, b, hb, hmem⟩ := hA k
  refine ⟨c * a + d, c * b, ?_, ?_⟩
  · have hmul : 1 * 1 ≤ c * b := Nat.mul_le_mul hc hb
    simpa using hmul
  · intro j hj
    have hmemj := hmem j hj
    have heq : (c * a + d) + (c * b) * j = c * (a + b * j) + d := by ring
    rw [heq]
    exact hmemj

end Commons.Combinatorics.Additive.AP
