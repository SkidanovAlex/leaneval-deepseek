import Mathlib

namespace Work.Peluse.BoxNorm

/-- Cauchy–Schwarz for a complex-valued sum: `‖∑ u i * conj (v i)‖² ≤ (∑ ‖u i‖²)(∑ ‖v i‖²)`.

This is the triangle inequality followed by the real Cauchy–Schwarz inequality
`Finset.sum_mul_sq_le_sq_mul_sq` applied to the nonnegative sequences `‖u i‖`, `‖v i‖`. -/
theorem cauchySchwarzC {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    ‖∑ i ∈ s, u i * star (v i)‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * (∑ i ∈ s, ‖v i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, u i * star (v i)‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
    calc ‖∑ i ∈ s, u i * star (v i)‖ ≤ ∑ i ∈ s, ‖u i * star (v i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by simp
  have h2 : (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * (∑ i ∈ s, ‖v i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖u i‖) (fun i => ‖v i‖)
  calc ‖∑ i ∈ s, u i * star (v i)‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * (∑ i ∈ s, ‖v i‖ ^ 2) := h2

end Work.Peluse.BoxNorm
