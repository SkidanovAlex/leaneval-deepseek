import Mathlib
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Kernels.SlashBounds

open scoped MatrixGroups

/-- Upper bound for `‖jFun γ τ‖` in terms of the scale `S τ = 1 + (im τ)⁻¹ + |τ|`:
since `j(γ,τ) = cτ + d` is linear in `τ`, it grows at most like `|τ| ≤ S τ`. -/
private lemma jFun_norm_le_scale (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    ‖jFun γ (τ : ℂ)‖ ≤ (‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖) * scale τ := by
  have h1 : ‖jFun γ (τ : ℂ)‖ ≤ ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := by
    rw [jFun_apply]
    calc ‖(γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)‖
        ≤ ‖(γ 1 0 : ℂ) * (τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := norm_add_le _ _
      _ = ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := by rw [norm_mul]
  have hA : (0:ℝ) ≤ ‖(γ 1 0 : ℂ)‖ := norm_nonneg _
  have hB : (0:ℝ) ≤ ‖(γ 1 1 : ℂ)‖ := norm_nonneg _
  have hn : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have hs : (1:ℝ) ≤ scale τ := one_le_scale τ
  calc ‖jFun γ (τ : ℂ)‖
      ≤ ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := h1
    _ ≤ ‖(γ 1 0 : ℂ)‖ * scale τ + ‖(γ 1 1 : ℂ)‖ * scale τ := by
        have h2 : ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ ≤ ‖(γ 1 0 : ℂ)‖ * scale τ :=
          mul_le_mul_of_nonneg_left hn hA
        have h3 : ‖(γ 1 1 : ℂ)‖ ≤ ‖(γ 1 1 : ℂ)‖ * scale τ := le_mul_of_one_le_right hB hs
        linarith
    _ = (‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖) * scale τ := by ring

/-- Lower bound for `‖jFun γ τ‖`: the factor of automorphy of an element of `SL(2,ℤ)` is
bounded below by `min 1 (im τ)`.  Equivalently `‖jFun γ τ‖⁻¹ ≤ S τ`. -/
private lemma jFun_inv_le_scale (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (‖jFun γ (τ : ℂ)‖)⁻¹ ≤ scale τ := by
  by_cases hc : (γ 1 0 : ℤ) = 0
  · -- `j(γ,τ) = d` is a nonzero integer, hence `|j| ≥ 1`.
    have h11 : γ 1 1 ≠ 0 := by
      intro h
      have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ).det) = 1 := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      rw [h, hc] at hdet
      norm_num at hdet
    have hj : jFun γ (τ : ℂ) = (γ 1 1 : ℂ) := by
      rw [jFun_apply, hc]; ring
    have h1 : (1:ℝ) ≤ ‖(γ 1 1 : ℂ)‖ := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h11
    rw [hj]
    calc ‖(γ 1 1 : ℂ)‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      _ ≤ scale τ := one_le_scale τ
  · -- `c ≠ 0`: then `im (cτ + d) = c * im τ` and `|c| ≥ 1`.
    have hcabs : (1:ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hc
    have him : (jFun γ (τ : ℂ)).im = ((γ 1 0 : ℤ) : ℝ) * τ.im := by
      rw [jFun_apply]
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
        UpperHalfPlane.coe_im]
      ring
    have hge : τ.im ≤ ‖jFun γ (τ : ℂ)‖ := by
      have h1 : |(jFun γ (τ : ℂ)).im| ≤ ‖jFun γ (τ : ℂ)‖ := Complex.abs_im_le_norm _
      rw [him, abs_mul, abs_of_pos τ.im_pos] at h1
      have h3 : τ.im ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := by
        calc τ.im = 1 * τ.im := (one_mul _).symm
          _ ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := mul_le_mul_of_nonneg_right hcabs τ.im_pos.le
      linarith
    have h4 : (‖jFun γ (τ : ℂ)‖)⁻¹ ≤ (τ.im)⁻¹ := by
      rw [inv_le_inv₀ (norm_pos_iff.mpr (jFun_ne_zero γ τ)) τ.im_pos]
      exact hge
    linarith [inv_im_le_scale τ]

lemma jFun_rpow_bound (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℝ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane,
      ‖jFun γ (τ : ℂ)‖ ^ m ≤ C * (scale τ) ^ N := by
  rcases le_or_gt 0 m with hm | hm
  · -- `m ≥ 0`: use the upper bound `‖jFun γ τ‖ ≤ K * S τ`.
    refine ⟨(‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖) ^ m, m,
      Real.rpow_nonneg (by positivity) m, hm, fun τ => ?_⟩
    calc ‖jFun γ (τ : ℂ)‖ ^ m ≤ ((‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖) * scale τ) ^ m :=
          Real.rpow_le_rpow (norm_nonneg _) (jFun_norm_le_scale γ τ) hm
      _ = (‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖) ^ m * (scale τ) ^ m :=
          Real.mul_rpow (by positivity) (scale_pos τ).le
  · -- `m < 0`: `‖jFun γ τ‖ ^ m = (‖jFun γ τ‖⁻¹) ^ (-m)` and `‖jFun γ τ‖⁻¹ ≤ S τ`.
    refine ⟨1, -m, zero_le_one, by linarith, fun τ => ?_⟩
    have hx : 0 ≤ ‖jFun γ (τ : ℂ)‖ := norm_nonneg _
    have hid : ‖jFun γ (τ : ℂ)‖ ^ m = ((‖jFun γ (τ : ℂ)‖)⁻¹) ^ (-m) := by
      have h1 : ((‖jFun γ (τ : ℂ)‖)⁻¹) ^ (-m) = ((‖jFun γ (τ : ℂ)‖) ^ (-m))⁻¹ :=
        Real.inv_rpow hx (-m)
      have h3 : ‖jFun γ (τ : ℂ)‖ ^ m = (‖jFun γ (τ : ℂ)‖ ^ (-m))⁻¹ := by
        have h2 := Real.rpow_neg hx (-m)
        rwa [neg_neg] at h2
      exact h3.trans h1.symm
    calc ‖jFun γ (τ : ℂ)‖ ^ m = ((‖jFun γ (τ : ℂ)‖)⁻¹) ^ (-m) := hid
      _ ≤ (scale τ) ^ (-m) :=
          Real.rpow_le_rpow (inv_nonneg.mpr hx) (jFun_inv_le_scale γ τ) (by linarith)
      _ = 1 * (scale τ) ^ (-m) := (one_mul _).symm

end Work.Kernels.SlashBounds
