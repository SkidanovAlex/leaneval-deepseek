import Mathlib
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.ModerateGrowth

open Work.Kernels

namespace Work.Kernels.SlashBounds

/-- A nonzero integer has absolute value at least one, as a real number. -/
private lemma one_le_abs_intCast {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ |((n : ℤ) : ℝ)| := by
  have h := Int.one_le_abs hn
  have h3 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.mpr h
  simpa [Int.cast_abs] using h3

lemma jFun_bound_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∀ τ : UpperHalfPlane, (‖jFun γ (τ : ℂ)‖)⁻¹ ≤ 1 + (τ.im)⁻¹ := by
  intro τ
  have him : 0 < τ.im := τ.im_pos
  have hpos : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr him.le
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · -- `γ 1 0 = 0`: then `jFun γ τ = γ 1 1`, a nonzero integer.
    have hd : γ 1 1 ≠ 0 := by
      intro hd
      have hdet := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at hdet
      rw [hc, hd] at hdet
      norm_num at hdet
    have hjr : jFun γ (τ : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by
      rw [jFun_apply, hc]
      simp
    have h1 : (1 : ℝ) ≤ ‖jFun γ (τ : ℂ)‖ := by
      rw [hjr, Complex.norm_intCast]
      exact one_le_abs_intCast hd
    calc (‖jFun γ (τ : ℂ)‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      _ ≤ 1 + (τ.im)⁻¹ := le_add_of_nonneg_right hpos
  · -- `γ 1 0 ≠ 0`: the imaginary part of `jFun γ τ` is `(γ 1 0) * im τ`.
    have hcle : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := one_le_abs_intCast hc
    have him_eq : (jFun γ (τ : ℂ)).im = (γ 1 0 : ℝ) * τ.im := by
      simp [jFun_apply, Complex.mul_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im]
    have h2 : τ.im ≤ |(jFun γ (τ : ℂ)).im| := by
      rw [him_eq, abs_mul, abs_of_pos him]
      simpa using mul_le_mul_of_nonneg_right hcle him.le
    have hle : τ.im ≤ ‖jFun γ (τ : ℂ)‖ := le_trans h2 (Complex.abs_im_le_norm _)
    calc (‖jFun γ (τ : ℂ)‖)⁻¹ ≤ (τ.im)⁻¹ := inv_anti₀ him hle
      _ ≤ 1 + (τ.im)⁻¹ := le_add_of_nonneg_left zero_le_one

end Work.Kernels.SlashBounds
