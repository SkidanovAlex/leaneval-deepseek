import Mathlib

namespace Work.Peluse.Peel

/-- Reindexing a bilinear `tsum` over `ℤ`: shifting the summation variable `x ↦ x + b`
turns `Φ (x + b) * star (Φ (x + a))` into `Φ y * star (Φ (y + (a - b)))`,
since `(x + b) + (a - b) = x + a`. -/
theorem tsum_shift_pair (Φ : ℤ → ℂ) (a b : ℤ) :
    (∑' x : ℤ, Φ (x + b) * star (Φ (x + a)))
      = ∑' y : ℤ, Φ y * star (Φ (y + (a - b))) := by
  have h : ∀ x : ℤ, x + b + (a - b) = x + a := by intro x; ring
  simpa [h] using
    Equiv.tsum_eq (Equiv.addRight b) (fun y : ℤ => Φ y * star (Φ (y + (a - b))))

end Work.Peluse.Peel
