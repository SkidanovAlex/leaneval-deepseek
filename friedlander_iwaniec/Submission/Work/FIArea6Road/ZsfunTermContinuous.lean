import Mathlib

namespace Work.FIArea6Road

/-- The exponent `-(σ + t·i)` is never zero when `0 < σ`. -/
theorem zsfunTerm_exp_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    -((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have h2 : ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 := neg_eq_zero.mp h
  have : σ = 0 := by rw [← h1, h2]; simp
  linarith

theorem ZsfunTermContinuous (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Continuous (fun t : ℝ => a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hf : Continuous (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
  exact Continuous.const_mul (hf.const_cpow (Or.inr (zsfunTerm_exp_ne_zero hσ))) (a n)

end Work.FIArea6Road
