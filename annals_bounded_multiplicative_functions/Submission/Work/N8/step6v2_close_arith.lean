import Mathlib
import Submission.Work.N8.step6v2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

lemma step6v2_close_arith (ℓ : ℕ) (P N L D : ℝ)
    (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hN : 0 < N) (hLDN : N * L ≤ 10 * D) :
    (ℓ : ℝ) * (2 * P) ^ ℓ * (200 * L / D) ≤ step6C0v2 ℓ * P ^ ℓ / N := by
  have hNL : N * L / D ≤ 10 := by rw [div_le_iff₀ hD]; linarith
  have key : (ℓ : ℝ) * (2 : ℝ) ^ ℓ * (200 * (N * L / D)) ≤ step6C0v2 ℓ := by
    have h1 : 200 * (N * L / D) ≤ 2000 := by nlinarith [hNL]
    have h2 : (0 : ℝ) ≤ (ℓ : ℝ) * (2 : ℝ) ^ ℓ := by positivity
    calc (ℓ : ℝ) * (2 : ℝ) ^ ℓ * (200 * (N * L / D))
        ≤ (ℓ : ℝ) * (2 : ℝ) ^ ℓ * 2000 := mul_le_mul_of_nonneg_left h1 h2
      _ = 2000 * ((ℓ : ℝ) * (2 : ℝ) ^ ℓ) := by ring
      _ ≤ 4000 * ((ℓ : ℝ) * (2 : ℝ) ^ ℓ) := mul_le_mul_of_nonneg_right (by norm_num) h2
      _ = 4000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ := by ring
      _ ≤ step6C0v2 ℓ := le_step6C0v2 ℓ
  calc (ℓ : ℝ) * (2 * P) ^ ℓ * (200 * L / D)
      = (ℓ : ℝ) * (2 : ℝ) ^ ℓ * P ^ ℓ * (200 * L / D) := by rw [mul_pow]; ring
    _ = ((ℓ : ℝ) * (2 : ℝ) ^ ℓ * (200 * (N * L / D))) * (P ^ ℓ / N) := by
          field_simp
    _ ≤ step6C0v2 ℓ * (P ^ ℓ / N) := mul_le_mul_of_nonneg_right key (by positivity)
    _ = step6C0v2 ℓ * P ^ ℓ / N := by ring

end Work.N8
