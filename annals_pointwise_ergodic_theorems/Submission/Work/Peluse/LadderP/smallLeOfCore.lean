import Mathlib
import Submission.Work.Peluse.LadderP.stepPCore

namespace Work.Peluse.LadderP

theorem smallLeOfCore (j n M₁ : ℕ) (L D : ℕ) {u γ η C C₅₁ cη : ℝ} {e e₅₁ : ℕ}
    (hC₅₁ : 0 < C₅₁) (he₅₁ : 1 ≤ e₅₁) (hu1 : u ≤ 1)
    (hη : η = cη * γ ^ (2 * e₅₁))
    (hcore : C * u ^ e ≤ C₅₁ * cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁))
    (hsmall : (D : ℝ) ≤ C * u ^ e * ((M₁ : ℝ) * (L : ℝ))) :
    (D : ℝ) ≤ C₅₁ * (γ * η) ^ e₅₁ * ((M₁ : ℝ) * (L : ℝ)) := by
  -- `(γ * η) ^ e₅₁ = cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁)`
  have hexp : e₅₁ + 2 * e₅₁ * e₅₁ = (1 + 2 * e₅₁) * e₅₁ := by ring
  have hγη : (γ * η) ^ e₅₁ = cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) := by
    calc (γ * η) ^ e₅₁
        = γ ^ e₅₁ * η ^ e₅₁ := by rw [mul_pow]
      _ = γ ^ e₅₁ * (cη * γ ^ (2 * e₅₁)) ^ e₅₁ := by rw [hη]
      _ = γ ^ e₅₁ * (cη ^ e₅₁ * (γ ^ (2 * e₅₁)) ^ e₅₁) := by rw [mul_pow]
      _ = γ ^ e₅₁ * (cη ^ e₅₁ * γ ^ (2 * e₅₁ * e₅₁)) := by rw [← pow_mul]
      _ = cη ^ e₅₁ * (γ ^ e₅₁ * γ ^ (2 * e₅₁ * e₅₁)) := by ring
      _ = cη ^ e₅₁ * γ ^ (e₅₁ + 2 * e₅₁ * e₅₁) := by rw [pow_add]
      _ = cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) := by rw [hexp]
  have hcore' : C * u ^ e ≤ C₅₁ * (γ * η) ^ e₅₁ := by
    rw [hγη, ← mul_assoc]
    exact hcore
  have hML : (0 : ℝ) ≤ (M₁ : ℝ) * (L : ℝ) := by positivity
  exact le_trans hsmall (mul_le_mul_of_nonneg_right hcore' hML)

end Work.Peluse.LadderP
