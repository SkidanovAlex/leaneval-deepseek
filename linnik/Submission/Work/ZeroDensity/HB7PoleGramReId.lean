import Mathlib

namespace Work.ZeroDensity

lemma HB7PoleGramReId {g y : ℝ} (hy : 0 < y) (Ψ : ℂ) :
    ((g : ℂ) * Ψ * (starRingEnd ℂ) Ψ / (y : ℂ)).re = g * ‖Ψ‖ ^ 2 / y := by
  have _ : (0 : ℝ) < y := hy
  have h : (g : ℂ) * Ψ * (starRingEnd ℂ) Ψ / (y : ℂ)
      = ((g * Complex.normSq Ψ / y : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj]
    push_cast
    ring
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Work.ZeroDensity
