import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_log_norm_im_sub_le

open Complex
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- **Two-sided Lipschitz bound for `log ‖Γ` along a vertical line.**
For `1/2 ≤ u₁, u₂ ≤ 8` and any real `v`,
`|log ‖Γ(u₁ + i v)‖ - log ‖Γ(u₂ + i v)‖| ≤ |u₁ - u₂| (log (2 + |v|) + 2)`.

This is the symmetric form of `log_norm_Gamma_sub_le`: the mean value theorem with the
derivative bound `|Re ψ(u + i v)| ≤ ‖ψ(u + i v)‖ ≤ log (2 + |v|) + 2`
(`digamma_mid_strip_le`). -/
lemma log_norm_Gamma_sub_abs_le (u₁ u₂ v : ℝ) (h1 : (1 : ℝ) / 2 ≤ u₁) (h1' : u₁ ≤ 8)
    (h2 : (1 : ℝ) / 2 ≤ u₂) (h2' : u₂ ≤ 8) :
    |Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * Complex.I)‖| ≤
      |u₁ - u₂| * (Real.log (2 + |v|) + 2) := by
  have key : ∀ a b : ℝ, (1 : ℝ) / 2 ≤ a → a ≤ b → b ≤ 8 →
      |Real.log ‖Complex.Gamma ((b : ℂ) + (v : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * Complex.I)‖| ≤
      (Real.log (2 + |v|) + 2) * (b - a) := by
    intro a b ha hab hb
    set F : ℝ → ℝ := fun u => Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ with hF
    set C : ℝ := Real.log (2 + |v|) + 2 with hC
    have hdiff : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ F u := by
      intro u hu
      have hu0 : 0 < u := by linarith [(Set.mem_Icc.mp hu).1, ha]
      exact (hasDerivAt_log_norm_Gamma u v hu0).differentiableAt
    have hbound : ∀ u ∈ Set.Icc a b, ‖deriv F u‖ ≤ C := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Set.mem_Icc.mp hu
      have hu0 : 0 < u := by linarith [hu1, ha]
      have hua : (1 : ℝ) / 2 ≤ u := le_trans ha hu1
      have hu8 : u ≤ 8 := le_trans hu2 hb
      have hderiv : deriv F u = (Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).re :=
        (hasDerivAt_log_norm_Gamma u v hu0).deriv
      rw [hderiv, Real.norm_eq_abs]
      have hψ : ‖Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C := by
        rw [hC]
        exact digamma_mid_strip_le u v hua hu8
      exact le_trans (Complex.abs_re_le_norm _) hψ
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc a b)
      (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
    simpa [hF, hC, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hmain
  rcases le_total u₁ u₂ with h | h
  · have hthis := key u₁ u₂ h1 h h2'
    have heq : |u₁ - u₂| * (Real.log (2 + |v|) + 2) =
        (Real.log (2 + |v|) + 2) * (u₂ - u₁) := by
      rw [abs_sub_comm u₁ u₂, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [heq]
    exact le_trans (le_of_eq (abs_sub_comm _ _)) hthis
  · have hthis := key u₂ u₁ h2 h h1'
    have heq : |u₁ - u₂| * (Real.log (2 + |v|) + 2) =
        (Real.log (2 + |v|) + 2) * (u₁ - u₂) := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [heq]
    exact hthis

theorem gammaR_log_norm_sub_le_im (x₁ x₂ T₀ T : ℝ) (h1 : 1 ≤ x₁) (h1' : x₁ ≤ 16)
    (h2 : 1 ≤ x₂) (h2' : x₂ ≤ 16) (hT₀ : 2 ≤ T₀) (hT : T₀ ≤ T) :
    Real.log ‖Complex.Gammaℝ ((x₁ : ℂ) + Complex.I * (T : ℂ))‖ -
        Real.log ‖Complex.Gammaℝ ((x₂ : ℂ) + Complex.I * (T₀ : ℂ))‖ ≤
      -(Real.pi / 4) * (T - T₀) + (x₁ / 2) * Real.log (T / T₀) + (1 / 4) * (T - T₀) +
        |x₁ - x₂| * ((Real.log (2 + |T₀ / 2|) + 4) / 2) + 2 * |x₁ - x₂| := by
  have hlogπ_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogπ_le : Real.log Real.pi ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  -- vertical increment for the first variable
  have him := Gamma_log_norm_im_sub_le (x₁ / 2) (T₀ / 2) (T / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hratio : (T / 2) / (T₀ / 2) = T / T₀ := by
    rw [div_div_div_cancel_right₀] <;> ring
    linarith
  rw [hratio] at him
  -- horizontal increment between the two variables
  have hBabs := log_norm_Gamma_sub_abs_le (x₁ / 2) (x₂ / 2) (T₀ / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hx : |x₁ / 2 - x₂ / 2| = |x₁ - x₂| / 2 := by
    rw [show x₁ / 2 - x₂ / 2 = (x₁ - x₂) / 2 by ring, abs_div]
    norm_num
  rw [hx] at hBabs
  have hB : Real.log ‖Complex.Gamma (((x₁ / 2 : ℝ) : ℂ) + ((T₀ / 2 : ℝ) : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (((x₂ / 2 : ℝ) : ℂ) + ((T₀ / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      |x₁ - x₂| * ((Real.log (2 + |T₀ / 2|) + 2) / 2) := by
    have h := le_abs_self (Real.log ‖Complex.Gamma (((x₁ / 2 : ℝ) : ℂ) +
      ((T₀ / 2 : ℝ) : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (((x₂ / 2 : ℝ) : ℂ) + ((T₀ / 2 : ℝ) : ℂ) * Complex.I)‖)
    linarith [h, hBabs]
  -- control the change of the `log π` prefactor
  have hπ : (x₂ / 2) * Real.log Real.pi - (x₁ / 2) * Real.log Real.pi ≤
      2 * |x₁ - x₂| := by
    have h1' : (x₂ / 2) * Real.log Real.pi - (x₁ / 2) * Real.log Real.pi =
        ((x₂ - x₁) / 2) * Real.log Real.pi := by ring
    rw [h1']
    rcases le_total x₁ x₂ with hc | hc
    · rw [abs_sub_comm x₁ x₂, abs_of_nonneg (sub_nonneg.mpr hc)]
      nlinarith [hlogπ_nn, hlogπ_le, hc]
    · rw [abs_of_nonneg (sub_nonneg.mpr hc)]
      nlinarith [hlogπ_nn, hc]
  -- expand both `Γℝ` terms
  have hGL : Real.log ‖Complex.Gammaℝ ((x₁ : ℂ) + Complex.I * (T : ℂ))‖ =
      -(x₁ / 2) * Real.log Real.pi +
        Real.log ‖Complex.Gamma (((x₁ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)‖ := by
    rw [log_norm_gammaR_eq x₁ T (by linarith)]
    rw [mul_comm Complex.I ((T / 2 : ℝ) : ℂ)]
  have hGR : Real.log ‖Complex.Gammaℝ ((x₂ : ℂ) + Complex.I * (T₀ : ℂ))‖ =
      -(x₂ / 2) * Real.log Real.pi +
        Real.log ‖Complex.Gamma (((x₂ / 2 : ℝ) : ℂ) + ((T₀ / 2 : ℝ) : ℂ) * Complex.I)‖ := by
    rw [log_norm_gammaR_eq x₂ T₀ (by linarith)]
    rw [mul_comm Complex.I ((T₀ / 2 : ℝ) : ℂ)]
  rw [hGL, hGR]
  nlinarith [him, hB, hπ, abs_nonneg (x₁ - x₂)]

end Commons.Analysis.SpecialFunctions.Gamma
