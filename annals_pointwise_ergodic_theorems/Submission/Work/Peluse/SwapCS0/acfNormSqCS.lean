import Mathlib

namespace Work.Peluse.SwapCS0

/-- Cauchy–Schwarz for the Hermitian pairing `∑ x ∈ s, u x * star (v x)`. -/
lemma acfNormSqCS {ι : Type} (s : Finset ι) (u v : ι → ℂ) :
    ‖∑ x ∈ s, u x * star (v x)‖ ^ 2 ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, u x * star (v x)‖ ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ := by
    calc ‖∑ x ∈ s, u x * star (v x)‖ ≤ ∑ x ∈ s, ‖u x * star (v x)‖ := norm_sum_le _ _
      _ = ∑ x ∈ s, ‖u x‖ * ‖v x‖ := by simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖u x‖) (fun x => ‖v x‖)
  have h3 : ‖∑ x ∈ s, u x * star (v x)‖ ^ 2 ≤ (∑ x ∈ s, ‖u x‖ * ‖v x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact le_trans h3 h2

end Work.Peluse.SwapCS0
