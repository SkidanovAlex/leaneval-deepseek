import Mathlib

namespace Work.FIArea7

/-- For a prime `p`, `Λ p / log p = 1`. -/
theorem psiVonMangoldtPrime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt p / Real.log (p : ℝ) = 1 := by
  have h := ArithmeticFunction.vonMangoldt_apply_prime hp
  rw [h]
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hne : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1)
  field_simp

end Work.FIArea7
