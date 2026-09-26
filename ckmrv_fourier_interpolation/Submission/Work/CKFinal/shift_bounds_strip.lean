import Mathlib
import Submission.Work.CKFinal.EngineDefs

namespace Work.CKFinal

open UpperHalfPlane

/-- Auxiliary: shifting the argument of an `UpperHalfPlane` point by `1` does not change
the imaginary part. -/
private lemma im_vadd_one {τ : UpperHalfPlane} (hτ : 3 / 2 ≤ τ.im) :
    3 / 2 ≤ ((1 : ℝ) +ᵥ τ).im := by
  rwa [UpperHalfPlane.vadd_im]

/-- Auxiliary norm estimate: `‖τ + 1‖ ≤ 1 + ‖τ‖` for `τ : ℍ`. -/
private lemma norm_vadd_one_le (τ : UpperHalfPlane) :
    ‖(((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)‖ ≤ 1 + ‖(τ : ℂ)‖ := by
  rw [UpperHalfPlane.coe_vadd]
  calc ‖(1 : ℂ) + (τ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ)‖ := norm_add_le _ _
    _ = 1 + ‖(τ : ℂ)‖ := by simp

/-- Auxiliary power estimate: `(1 + ‖τ+1‖)^A ≤ 2^A (1 + ‖τ‖)^A` for `A ≥ 0`. -/
private lemma rpow_vadd_one_le (A : ℝ) (hA : 0 ≤ A) (τ : UpperHalfPlane) :
    (1 + ‖(((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)‖) ^ A
      ≤ (2 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A := by
  calc (1 + ‖(((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)‖) ^ A
      ≤ (2 * (1 + ‖(τ : ℂ)‖)) ^ A :=
        Real.rpow_le_rpow (by positivity)
          (by linarith [norm_vadd_one_le τ, norm_nonneg (τ : ℂ)]) hA
    _ = (2 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A := Real.mul_rpow (by norm_num) (by positivity)

theorem shift_bounds_strip (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (f : UpperHalfPlane → ℂ)
    (hf : ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im → ‖f τ‖ ≤ K * (1 + ‖(τ : ℂ)‖) ^ A) :
    (∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
        ‖Work.CKFinal.shiftB f τ‖ ≤ K * (2 ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A) ∧
    (∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
        ‖Work.CKFinal.shiftA f τ‖ ≤ K * (2 ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ (A + 1)) := by
  have h2A : (0 : ℝ) ≤ (2 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) A
  constructor
  · -- bound for `shiftB f τ = f (τ+1) - f τ`
    intro τ hτ
    have h1 := hf τ hτ
    have h2 := hf ((1 : ℝ) +ᵥ τ) (im_vadd_one hτ)
    have h2' : ‖f ((1 : ℝ) +ᵥ τ)‖ ≤ K * ((2 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) :=
      le_trans h2 (mul_le_mul_of_nonneg_left (rpow_vadd_one_le A hA τ) hK)
    calc ‖shiftB f τ‖ = ‖f ((1 : ℝ) +ᵥ τ) - f τ‖ := rfl
      _ ≤ ‖f ((1 : ℝ) +ᵥ τ)‖ + ‖f τ‖ := norm_sub_le _ _
      _ ≤ K * ((2 : ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) + K * (1 + ‖(τ : ℂ)‖) ^ A :=
            add_le_add h2' h1
      _ = K * ((2 : ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A := by ring
  · -- bound for `shiftA f τ = f τ - τ (f (τ+1) - f τ) = (1+τ) f τ - τ f (τ+1)`
    intro τ hτ
    set u : ℝ := ‖(τ : ℂ)‖ with hu_def
    have hu : 0 ≤ u := by rw [hu_def]; positivity
    have hc : 0 < 1 + u := by linarith
    have h1 : ‖f τ‖ ≤ K * (1 + u) ^ A := by rw [hu_def]; exact hf τ hτ
    have h2 := hf ((1 : ℝ) +ᵥ τ) (im_vadd_one hτ)
    have h2' : ‖f ((1 : ℝ) +ᵥ τ)‖ ≤ K * ((2 : ℝ) ^ A * (1 + u) ^ A) := by
      refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ hK)
      rw [hu_def]; exact rpow_vadd_one_le A hA τ
    have hle1 : ‖(1 : ℂ) + (τ : ℂ)‖ ≤ 1 + u := by
      calc ‖(1 : ℂ) + (τ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ)‖ := norm_add_le _ _
        _ = 1 + u := by simp [hu_def]
    have hkey : shiftA f τ = (1 + (τ : ℂ)) * f τ - (τ : ℂ) * f ((1 : ℝ) +ᵥ τ) := by
      simp only [shiftA, shiftB]; ring
    rw [hkey]
    have t1 : ‖(1 + (τ : ℂ)) * f τ‖ ≤ K * (1 + u) ^ (A + 1) := by
      rw [norm_mul]
      refine le_trans (mul_le_mul hle1 h1 (norm_nonneg _) (by linarith)) (le_of_eq ?_)
      rw [Real.rpow_add hc A 1, Real.rpow_one]; ring
    have t2 : ‖(τ : ℂ) * f ((1 : ℝ) +ᵥ τ)‖ ≤ K * (2 : ℝ) ^ A * (1 + u) ^ (A + 1) := by
      rw [norm_mul, show ‖(τ : ℂ)‖ = u from hu_def.symm]
      have hK2A : 0 ≤ K * ((2 : ℝ) ^ A * (1 + u) ^ A) :=
        mul_nonneg hK (mul_nonneg h2A (Real.rpow_nonneg (by linarith) A))
      have step1 : u * ‖f ((1 : ℝ) +ᵥ τ)‖ ≤ u * (K * ((2 : ℝ) ^ A * (1 + u) ^ A)) :=
        mul_le_mul_of_nonneg_left h2' hu
      have step2 : u * (K * ((2 : ℝ) ^ A * (1 + u) ^ A))
          ≤ (1 + u) * (K * ((2 : ℝ) ^ A * (1 + u) ^ A)) :=
        mul_le_mul_of_nonneg_right (by linarith) hK2A
      have step3 : (1 + u) * (K * ((2 : ℝ) ^ A * (1 + u) ^ A))
          = K * (2 : ℝ) ^ A * (1 + u) ^ (A + 1) := by
        rw [Real.rpow_add hc A 1, Real.rpow_one]; ring
      exact le_trans step1 (le_trans step2 (le_of_eq step3))
    calc ‖(1 + (τ : ℂ)) * f τ - (τ : ℂ) * f ((1 : ℝ) +ᵥ τ)‖
        ≤ ‖(1 + (τ : ℂ)) * f τ‖ + ‖(τ : ℂ) * f ((1 : ℝ) +ᵥ τ)‖ := norm_sub_le _ _
      _ ≤ K * (1 + u) ^ (A + 1) + K * (2 : ℝ) ^ A * (1 + u) ^ (A + 1) := add_le_add t1 t2
      _ = K * ((2 : ℝ) ^ A + 1) * (1 + u) ^ (A + 1) := by ring

end Work.CKFinal
