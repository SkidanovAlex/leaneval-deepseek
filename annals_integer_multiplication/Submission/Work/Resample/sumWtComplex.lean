import Mathlib

namespace Work.Resample

theorem sumWtComplex (L : ℕ) (W : ℕ → ℤ) (z : ℕ → ℤ × ℤ) :
    ((∑ i ∈ Finset.range L, W i * (z i).1 : ℤ) : ℂ) +
      ((∑ i ∈ Finset.range L, W i * (z i).2 : ℤ) : ℂ) * Complex.I =
    ∑ i ∈ Finset.range L, (W i : ℂ) * (((z i).1 : ℂ) + ((z i).2 : ℂ) * Complex.I) := by
  push_cast
  have h : ∀ i : ℕ, (W i : ℂ) * ((z i).1 + (z i).2 * Complex.I)
      = (W i : ℂ) * (z i).1 + ((W i : ℂ) * (z i).2) * Complex.I := by intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, ← Finset.sum_mul]

end Work.Resample
