import Mathlib

namespace Work.Assembly

theorem exp_neg_le_pow (ρ γ : ℝ) (f : ℕ) (hρ : 0 < ρ) (h : -(γ / 4) ≤ Real.log ρ) :
    (Real.exp (-(γ / 2))) ^ f ≤ ρ ^ (2 * f) := by
  have h2 : -(γ / 2) ≤ Real.log (ρ ^ 2) := by
    rw [Real.log_pow]
    push_cast
    linarith [h]
  have h3 : Real.exp (-(γ / 2)) ≤ ρ ^ 2 := by
    rw [← Real.exp_log (pow_pos hρ 2)]
    exact Real.exp_le_exp.mpr h2
  calc (Real.exp (-(γ / 2))) ^ f ≤ (ρ ^ 2) ^ f :=
        pow_le_pow_left₀ (Real.exp_nonneg _) h3 f
    _ = ρ ^ (2 * f) := (pow_mul ρ 2 f).symm

end Work.Assembly
