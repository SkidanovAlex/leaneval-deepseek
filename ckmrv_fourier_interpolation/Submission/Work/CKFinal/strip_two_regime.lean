import Mathlib
import Submission.Work.CKFinal.rpow_exp_neg_bound
import Submission.Work.CKFinal.mid_strip_bound
import Submission.Work.CKFinal.tail_strip_bound

/-!
# `strip_two_regime`

Given nonnegative data `C, α₀, γ₀` and nonnegative exponents `β₀, δ₀`, there are a
constant `α ≥ 0` and an exponent `β > 0` such that the single power bound `α · y ^ (-β)`
dominates both

* the exponential tail `C · (2 + y) · exp (-(2π y))` for `y ≥ 2`, and
* the two-regime ("mid") bound `α₀ · y ^ (-β₀) + γ₀ · 3 ^ δ₀` for `0 < y ≤ 2`.

The construction is explicit: take `β = β₀ + 1` and
`α = max ((α₀ + γ₀ 3 ^ δ₀) · 2 ^ β) (2 C ((β+1)/(2π e)) ^ (β+1))`.
The two estimates are provided by `tail_strip_bound` and `mid_strip_bound`.
-/

namespace Work.CKFinal

theorem strip_two_regime (C β₀ α₀ γ₀ δ₀ : ℝ) (hC : 0 ≤ C) (hα₀ : 0 ≤ α₀) (hβ₀ : 0 ≤ β₀)
    (hγ₀ : 0 ≤ γ₀) (hδ₀ : 0 ≤ δ₀) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
      (∀ y : ℝ, 2 ≤ y → C * (2 + y) * Real.exp (-(2 * Real.pi * y)) ≤ α * y ^ (-β)) ∧
      (∀ y : ℝ, 0 < y → y ≤ 2 → α₀ * y ^ (-β₀) + γ₀ * 3 ^ δ₀ ≤ α * y ^ (-β)) := by
  set b := β₀ + 1 with hbdef
  have hbpos : 0 < b := by rw [hbdef]; linarith
  have hbnn : 0 ≤ b := hbpos.le
  have hble : β₀ ≤ b := by rw [hbdef]; linarith
  set A := (α₀ + γ₀ * 3 ^ δ₀) * 2 ^ b with hAdef
  set B := 2 * C * ((b + 1) / (2 * Real.pi * Real.exp 1)) ^ (b + 1) with hBdef
  have h3 : (0 : ℝ) < 3 ^ δ₀ := Real.rpow_pos_of_pos (by norm_num) δ₀
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (add_nonneg hα₀ (mul_nonneg hγ₀ h3.le))
      (Real.rpow_nonneg (by norm_num) b)
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by linarith)
      (Real.rpow_nonneg (by positivity) (b + 1))
  refine ⟨max A B, b, le_trans hA0 (le_max_left A B), hbpos, ?_, ?_⟩
  · intro y hy
    have hy0 : 0 ≤ y := by linarith
    have h1 := tail_strip_bound C b hC hbnn y hy
    calc C * (2 + y) * Real.exp (-(2 * Real.pi * y)) ≤ B * y ^ (-b) := h1
      _ ≤ max A B * y ^ (-b) :=
          mul_le_mul_of_nonneg_right (le_max_right A B) (Real.rpow_nonneg hy0 (-b))
  · intro y hy0 hy2
    have h1 := mid_strip_bound α₀ β₀ γ₀ δ₀ b hα₀ hβ₀ hγ₀ hδ₀ hble y hy0 hy2
    calc α₀ * y ^ (-β₀) + γ₀ * 3 ^ δ₀ ≤ A * y ^ (-b) := by rw [hAdef]; exact h1
      _ ≤ max A B * y ^ (-b) :=
          mul_le_mul_of_nonneg_right (le_max_left A B) (Real.rpow_nonneg hy0.le (-b))

end Work.CKFinal
