import Mathlib
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

namespace Commons.NumberTheory.Zeta

/-- The Riemann zeta function is `O(log)` on the strip `1 ≤ Re s ≤ 3`, in the form
`‖ζ(σ + iτ)‖ ≤ C (log(τ+3) + 1)` for `τ ≥ 3`. -/
theorem zeta_norm_le_log_one_le_re :
    ∃ C : ℝ, 0 < C ∧ ∀ τ σ : ℝ, (1 : ℝ) ≤ σ → σ ≤ 3 → 3 ≤ τ →
      ‖riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C * (Real.log (τ + 3) + 1) := by
  refine ⟨5, by norm_num, ?_⟩
  intro τ σ hσ _hσ3 hτ
  have hτ0 : (0 : ℝ) ≤ τ := by linarith
  have hτabs : |τ| = τ := abs_of_nonneg hτ0
  have hτ1 : (1 : ℝ) ≤ |τ| := by rw [hτabs]; linarith
  have h := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log (σ := σ) (t := τ) hσ hτ1
  rw [hτabs] at h
  have hlog : Real.log (τ + 2) ≤ Real.log (τ + 3) + 1 := by
    have hmono : Real.log (τ + 2) ≤ Real.log (τ + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hmain : ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 5 * (Real.log (τ + 3) + 1) := by
    calc
      ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 5 * Real.log (τ + 2) := h
      _ ≤ 5 * (Real.log (τ + 3) + 1) := by linarith
  rwa [mul_comm (τ : ℂ) Complex.I] at hmain

end Commons.NumberTheory.Zeta
