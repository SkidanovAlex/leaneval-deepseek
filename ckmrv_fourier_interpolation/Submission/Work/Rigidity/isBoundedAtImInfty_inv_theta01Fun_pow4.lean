/-
# Boundedness of `(θ₀₁)⁻⁴` at the cusp `i∞`

`θ₀₁ τ = θ₀₀ (τ + 1) = jacobiTheta (τ + 1)` tends to `1` as `im τ → ∞`: Mathlib's estimate
`norm_jacobiTheta_sub_one_le` gives
`‖θ₀₁ τ - 1‖ ≤ 2 / (1 - e^{-π y}) · e^{-π y}`  with `y = im τ`,
which is at most `1/2` once `e^{-π y} ≤ 1/16`.  Hence `‖θ₀₁ τ‖ ≥ 1/2` for `im τ ≥ log 16 / π`,
and therefore `‖(θ₀₁ τ)⁻⁴‖ = ‖θ₀₁ τ‖⁻⁴ ≤ 2⁴ = 16` in that range.  This is exactly
`UpperHalfPlane.IsBoundedAtImInfty`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP

namespace Work.Rigidity

open UpperHalfPlane

/-- The quantitative decay of `θ₀₁ - 1` at the cusp: with `y = im τ`,
`‖θ₀₁ τ - 1‖ ≤ 2 / (1 - e^{-π y}) · e^{-π y}`. -/
private lemma theta01Fun_sub_one_bound (τ : ℍ) :
    ‖Work.Kernels.theta01Fun τ - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) := by
  have h := norm_jacobiTheta_sub_one_le (τ := (τ : ℂ) + 1) (by simpa using τ.im_pos)
  have h' : ‖jacobiTheta ((τ : ℂ) + 1) - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) := by
    simpa using h
  have heq : Work.Kernels.theta01Fun τ = jacobiTheta ((τ : ℂ) + 1) := by
    simp only [Work.Kernels.theta01Fun]
    exact Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one (τ : ℂ)
  rw [heq]
  exact h'

/-- For `im τ ≥ log 16 / π` one has `‖(θ₀₁ τ)⁻⁴‖ ≤ 16`. -/
private lemma inv_theta01Fun_pow4_bound (τ : ℍ) (hτ : Real.log 16 / Real.pi ≤ τ.im) :
    ‖((Work.Kernels.theta01Fun τ) ^ 4)⁻¹‖ ≤ 16 := by
  have hbound := theta01Fun_sub_one_bound τ
  -- `log 16 ≤ π · im τ`
  have hlog : Real.log 16 ≤ Real.pi * τ.im := by
    have h := mul_le_mul_of_nonneg_right hτ Real.pi_pos.le
    rw [div_mul_cancel₀ _ Real.pi_ne_zero] at h
    linarith [h]
  -- `e^{-π im τ} ≤ 1/16`
  have hexp_le : Real.exp (-Real.pi * τ.im) ≤ 1 / 16 := by
    have h1 : -Real.pi * τ.im ≤ -Real.log 16 := by linarith [hlog]
    have h2 : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.log 16) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-Real.log 16) = 1 / 16 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
      norm_num
    rwa [h3] at h2
  -- consequently `‖θ₀₁ τ - 1‖ ≤ 1/2`
  have hstep : 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) ≤ 1 / 2 := by
    have hden : (15 / 16 : ℝ) ≤ 1 - Real.exp (-Real.pi * τ.im) := by linarith [hexp_le]
    have h1 : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 2 / (15 / 16 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    have he : (0 : ℝ) ≤ Real.exp (-Real.pi * τ.im) := (Real.exp_pos _).le
    calc 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im)
        ≤ (2 / (15 / 16 : ℝ)) * (1 / 16) :=
          mul_le_mul h1 hexp_le he (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  -- reverse triangle inequality gives `‖θ₀₁ τ‖ ≥ 1/2`
  have hnorm : (1 / 2 : ℝ) ≤ ‖Work.Kernels.theta01Fun τ‖ := by
    have hrt := abs_norm_sub_norm_le (Work.Kernels.theta01Fun τ) (1 : ℂ)
    rw [abs_le, norm_one] at hrt
    have hsub : ‖Work.Kernels.theta01Fun τ - 1‖ ≤ 1 / 2 := le_trans hbound hstep
    linarith [hrt.1, hrt.2, hsub]
  have hinv : ‖Work.Kernels.theta01Fun τ‖⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num) hnorm
    rw [one_div, one_div] at h
    norm_num at h
    exact h
  rw [norm_inv, norm_pow, ← inv_pow]
  calc (‖Work.Kernels.theta01Fun τ‖⁻¹) ^ 4 ≤ 2 ^ 4 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv 4
    _ = 16 := by norm_num

theorem isBoundedAtImInfty_inv_theta01Fun_pow4 :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => ((Work.Kernels.theta01Fun τ) ^ 4)⁻¹) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  exact ⟨16, Real.log 16 / Real.pi, inv_theta01Fun_pow4_bound⟩

end Work.Rigidity
