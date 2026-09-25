import Mathlib

namespace Work.Assembly

theorem exp_halves_pow (γ : ℝ) (f : ℕ) :
    (Real.exp γ) ^ f * (Real.exp (-(γ / 2))) ^ f = (Real.exp (γ / 2)) ^ f := by
  rw [← mul_pow, ← Real.exp_add]
  congr 1
  ring_nf

end Work.Assembly
