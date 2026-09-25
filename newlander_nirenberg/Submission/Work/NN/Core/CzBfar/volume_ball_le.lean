import Mathlib

namespace Work.NN.Core.CzBfar

open MeasureTheory MeasureTheory.Measure ENNReal

/-- The volume of a ball in `ℂ^n` (equipped with the product Lebesgue measure) grows like
`ρ ^ (2 * n)`: with `C = π ^ n` we have `volume (ball c ρ) ≤ C * ρ ^ (2 * n)`. -/
theorem volume_ball_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Fin n → ℂ) (ρ : ℝ), 0 < ρ →
      (MeasureTheory.volume (Metric.ball c ρ)).toReal ≤ C * ρ ^ (2 * n) := by
  have _ : 0 < n := hn
  refine ⟨Real.pi ^ n, pow_pos Real.pi_pos n, fun c ρ hρ => ?_⟩
  have hvol : MeasureTheory.volume (Metric.ball c ρ)
      = ENNReal.ofReal (Real.pi ^ n * ρ ^ (2 * n)) := by
    rw [MeasureTheory.volume_pi_ball c hρ]
    simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), NNReal.coe_real_pi]
    rw [hpi, ← ENNReal.ofReal_pow hρ.le 2,
      ← ENNReal.ofReal_mul (p := ρ ^ 2) (q := Real.pi) (by positivity)]
    rw [show ρ ^ 2 * Real.pi = Real.pi * ρ ^ 2 by ring]
    rw [← ENNReal.ofReal_pow (by positivity) n]
    congr 1
    rw [mul_pow, ← pow_mul]
  rw [hvol, ENNReal.toReal_ofReal (by positivity)]

end Work.NN.Core.CzBfar
