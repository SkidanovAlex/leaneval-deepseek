import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS

namespace Work.CKFinal

open Work.Kernels

/-! ## The three `z`-factors appearing in the `d = 8` `K_-` funnel estimate

All three are of the shape `(bounded factor) · (O(e^{-π Im z}) factor)` on the funnel
`{Im z ≥ 1/3}`, so each decays like `e^{-π Im z}` there. -/

/-- `‖E₁₀(z)·𝓛_S(z)‖ = O(e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma E10Fun_mul_LS_bound_third (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖E10Fun z * ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨CLS, hCLS, hLS⟩ := Work.Asymptotics.LS_exp_bound_third ℓ
  obtain ⟨cE4, hcE4, hE4⟩ := Work.Asymptotics.E4Fun_bound_third
  obtain ⟨cE6, hcE6, hE6⟩ := Work.Asymptotics.E6Fun_bound_third
  refine ⟨cE4 * cE6 * CLS + 1, by positivity, fun z hz => ?_⟩
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have h4 := hE4 z hz
  have h6 := hE6 z hz
  have hS := hLS z hz
  have hrepr : ‖E10Fun z * ℓ.L_S z‖ = ‖E4Fun z‖ * ‖E6Fun z‖ * ‖ℓ.L_S z‖ := by
    rw [show E10Fun z = E4Fun z * E6Fun z from rfl, norm_mul, norm_mul]
  rw [hrepr]
  calc ‖E4Fun z‖ * ‖E6Fun z‖ * ‖ℓ.L_S z‖
      ≤ cE4 * cE6 * (CLS * Real.exp (-(Real.pi * z.im))) := by
        have h1 : ‖E4Fun z‖ * ‖E6Fun z‖ ≤ cE4 * cE6 :=
          mul_le_mul h4 h6 (norm_nonneg _) hcE4.le
        exact mul_le_mul h1 hS (norm_nonneg _) (by positivity)
    _ = (cE4 * cE6 * CLS) * Real.exp (-(Real.pi * z.im)) := by ring
    _ ≤ (cE4 * cE6 * CLS + 1) * Real.exp (-(Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_right (by linarith) he0

/-- `‖E₈(z)·V(z)‖ = O(e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma E8Fun_mul_VFun_bound_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖E8Fun z * VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨cV, hcV, hV⟩ := Work.Asymptotics.VFun_bound_third
  obtain ⟨cE4, hcE4, hE4⟩ := Work.Asymptotics.E4Fun_bound_third
  refine ⟨cE4 ^ 2 * cV + 1, by positivity, fun z hz => ?_⟩
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have h4 := hE4 z hz
  have hVz := hV z hz
  have hrepr : ‖E8Fun z * VFun z‖ = ‖E4Fun z‖ ^ 2 * ‖VFun z‖ := by
    rw [show E8Fun z = E4Fun z ^ 2 from rfl, norm_mul, norm_pow]
  rw [hrepr]
  have hE8 : ‖E4Fun z‖ ^ 2 ≤ cE4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  calc ‖E4Fun z‖ ^ 2 * ‖VFun z‖ ≤ cE4 ^ 2 * (cV * Real.exp (-(Real.pi * z.im))) :=
        mul_le_mul hE8 hVz (norm_nonneg _) (by positivity)
    _ = (cE4 ^ 2 * cV) * Real.exp (-(Real.pi * z.im)) := by ring
    _ ≤ (cE4 ^ 2 * cV + 1) * Real.exp (-(Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_right (by linarith) he0

/-- `‖E₆(z)·(U(z)² - W(z)²)‖ = O(e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma E6Fun_mul_UW_bound_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖E6Fun z * (UFun z ^ 2 - WFun z ^ 2)‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨c2, hc2, h2⟩ := Work.Asymptotics.UFun_sq_sub_WFun_sq_bound_third
  obtain ⟨cE6, hcE6, hE6⟩ := Work.Asymptotics.E6Fun_bound_third
  refine ⟨cE6 * c2 + 1, by positivity, fun z hz => ?_⟩
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have h6 := hE6 z hz
  have h2z := h2 z hz
  rw [norm_mul]
  calc ‖E6Fun z‖ * ‖UFun z ^ 2 - WFun z ^ 2‖
      ≤ cE6 * (c2 * Real.exp (-(Real.pi * z.im))) :=
        mul_le_mul h6 h2z (norm_nonneg _) hcE6.le
    _ = (cE6 * c2) * Real.exp (-(Real.pi * z.im)) := by ring
    _ ≤ (cE6 * c2 + 1) * Real.exp (-(Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_right (by linarith) he0

/-- The `z`-factorisation `E₁₀𝓛_S`, `E₈V`, `E₆(U² - W²)` on the funnel `{Im z ≥ 1/3}`:
each is `O(e^{-π Im z})`. -/
theorem Ncusp8DB_zfact (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ∧
      ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C₁, hC₁, h1⟩ := E10Fun_mul_LS_bound_third ℓ
  obtain ⟨C₂, hC₂, h2⟩ := E8Fun_mul_VFun_bound_third
  obtain ⟨C₃, hC₃, h3⟩ := E6Fun_mul_UW_bound_third
  refine ⟨max (max C₁ C₂) C₃, by positivity, fun z hz => ⟨?_, ?_, ?_⟩⟩
  · exact le_trans (h1 z hz)
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left C₁ C₂) (le_max_left _ C₃))
        (Real.exp_pos _).le)
  · exact le_trans (h2 z hz)
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right C₁ C₂) (le_max_left _ C₃))
        (Real.exp_pos _).le)
  · exact le_trans (h3 z hz)
      (mul_le_mul_of_nonneg_right (le_max_right _ C₃) (Real.exp_pos _).le)

end Work.CKFinal
