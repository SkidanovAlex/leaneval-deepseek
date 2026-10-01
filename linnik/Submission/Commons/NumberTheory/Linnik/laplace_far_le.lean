import Mathlib
import Submission.Commons.Analysis.Complex.laplace_bound_two_sided

namespace Commons.NumberTheory.Linnik

theorem laplace_far_le {x₀ B M δ L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hδ : 0 < δ) (hL : 0 < L) {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)) (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {a η : ℝ} (ha : |a| ≤ M) (hη : δ / 2 * L ≤ |η|) : ‖∫ t in (0:ℝ)..x₀, Complex.exp (-((((a : ℂ) + (η : ℂ) * Complex.I)) * (t : ℂ))) * f t‖ ≤ ‖f 0‖ / (δ / 2 * L) + (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 := by
  set z : ℂ := (a : ℂ) + (η : ℂ) * Complex.I with hz
  have hzre : z.re = a := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  have hδL : 0 < δ / 2 * L := by positivity
  have hηnorm : δ / 2 * L ≤ ‖z‖ := by
    calc δ / 2 * L ≤ |η| := hη
      _ = |z.im| := by rw [hzim]
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hδL hηnorm
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hzpos; simp at hzpos
  have hmain := Commons.Analysis.Complex.laplace_bound_two_sided hx₀ hB hcont hf2 hBnd hvan hz0
  have hgoal_eq : (∫ t in (0:ℝ)..x₀, Complex.exp (-((((a : ℂ) + (η : ℂ) * Complex.I)) * (t : ℂ))) * f t)
      = ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t := by
    rw [← hz]
  rw [hgoal_eq]
  refine le_trans hmain ?_
  have hexp : Real.exp (x₀ * |z.re|) ≤ Real.exp (x₀ * M) := by
    apply Real.exp_le_exp.mpr
    rw [hzre]
    exact mul_le_mul_of_nonneg_left ha hx₀.le
  have hnum : 0 ≤ 2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀ := by positivity
  have h1 : ‖f 0‖ / ‖z‖ ≤ ‖f 0‖ / (δ / 2 * L) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hδL hηnorm
  have h2 : (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * |z.re|) / ‖z‖ ^ 2
      ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 := by
    apply div_le_div₀ (mul_nonneg hnum (Real.exp_pos _).le) _ (by positivity) _
    · exact mul_le_mul_of_nonneg_left hexp hnum
    · exact pow_le_pow_left₀ hδL.le hηnorm 2
  linarith

end Commons.NumberTheory.Linnik
