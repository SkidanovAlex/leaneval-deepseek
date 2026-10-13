import Mathlib

namespace Work.WilkG4c

/-- `MvPolynomial.eval` with natural coefficients is monotone in the evaluation point. -/
theorem eval_mono {σ : Type*} (b : MvPolynomial σ ℕ) {x y : σ → ℕ} (h : ∀ i, x i ≤ y i) :
    MvPolynomial.eval x b ≤ MvPolynomial.eval y b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [MvPolynomial.eval_add]; exact add_le_add hp hq
  | mul_X p n hp =>
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h n)

end Work.WilkG4c
