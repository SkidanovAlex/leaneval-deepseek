import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

open scoped Real

/-- **The cosine polynomial of the far-zero zero-free region.**

`Q(θ) = 5/4 + 2 cos θ + cos 2θ + (1/4) cos 3θ = (1 + cos θ)·(cos θ + 1/2)² ≥ 0`, i.e. the
coefficients `(a₀,a₁,a₂,a₃) = (5/4, 2, 1, 1/4)` are nonnegative and reproduce the manifestly
nonnegative factorisation; and `2·(√a₁ - √a₀)²/(a₁+a₂+a₃) ≥ 1/25`, the numerical input of the
zero-free-region computation (`F = (√2-√(5/4))²/(13/4) = 13/4 - √10`). -/
theorem cosPolyDecent :
    (∀ θ : ℝ, (5 / 4 : ℝ) + 2 * Real.cos θ + Real.cos (2 * θ) + (1 / 4) * Real.cos (3 * θ)
        = (1 + Real.cos θ) * (Real.cos θ + 1 / 2) ^ 2) ∧
    (∀ θ : ℝ, 0 ≤ (5 / 4 : ℝ) + 2 * Real.cos θ + Real.cos (2 * θ) + (1 / 4) * Real.cos (3 * θ)) ∧
    (1 / 25 : ℝ) ≤ 2 * (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 / (13 / 4) := by
  constructor
  · intro θ
    rw [Real.cos_two_mul, Real.cos_three_mul]
    ring
  constructor
  · intro θ
    have h1 : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
    have h2 : 0 ≤ (Real.cos θ + 1 / 2) ^ 2 := sq_nonneg _
    calc (0 : ℝ) ≤ (1 + Real.cos θ) * (Real.cos θ + 1 / 2) ^ 2 := mul_nonneg h1 h2
      _ = 5 / 4 + 2 * Real.cos θ + Real.cos (2 * θ) + (1 / 4) * Real.cos (3 * θ) := by
        rw [Real.cos_two_mul, Real.cos_three_mul]; ring
  · have h5 : Real.sqrt (5 / 4) = Real.sqrt 5 / 2 := by
      have h : (0 : ℝ) ≤ Real.sqrt 5 / 2 := by positivity
      have h2 : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num
      rw [← h2]
      exact Real.sqrt_sq h
    have h10 : Real.sqrt 2 * Real.sqrt 5 = Real.sqrt 10 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have hexp : (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 = 13 / 4 - Real.sqrt 10 := by
      rw [h5]
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h5' : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num
      have key : (Real.sqrt 2 - Real.sqrt 5 / 2) ^ 2
          = 2 - Real.sqrt 2 * Real.sqrt 5 + 5 / 4 := by
        rw [sub_sq, h2, h5']; ring
      rw [key, h10]
      ring
    rw [hexp]
    have h1 : 2 * (13 / 4 - Real.sqrt 10) / (13 / 4) = 2 - 8 * Real.sqrt 10 / 13 := by
      field_simp
      ring
    rw [h1]
    have h10' : Real.sqrt 10 ≤ 637 / 200 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    nlinarith [h10']

end Work.LinnikAreas.OtherCharRepel
