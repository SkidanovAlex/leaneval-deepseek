import Mathlib
import Submission.Work.ZeroFreeTables.tf71Q_defs
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-! ## Elementary trigonometric rewrites in terms of `tan θ`

For `0 < θ < π/2` we have `cos θ ≠ 0`, hence `sin θ = tan θ · cos θ` and
`cos²θ = 1/(1+tan²θ)`; the values of `sin 2θ`, `cos 2θ` follow.
-/

lemma tf71Qsub_cos_sq (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) :
    Real.cos θ ^ 2 = 1/(1 + Real.tan θ^2) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin : Real.sin θ = Real.tan θ * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hcos]
  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [hsin] at h1
  have hT : (1 + Real.tan θ^2) ≠ 0 := by positivity
  rw [eq_div_iff hT]
  nlinarith [h1]

lemma tf71Qsub_sin_two_mul (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) :
    Real.sin (2*θ) = 2 * Real.tan θ / (1 + Real.tan θ^2) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin : Real.sin θ = Real.tan θ * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hcos]
  have hsq := tf71Qsub_cos_sq θ hθ0 hθ1
  have hsin2' : Real.sin (2*θ) = 2 * Real.tan θ * Real.cos θ ^ 2 := by
    rw [Real.sin_two_mul, hsin]; ring
  rw [hsin2', hsq]
  field_simp

lemma tf71Qsub_cos_two_mul (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) :
    Real.cos (2*θ) = (1 - Real.tan θ^2)/(1 + Real.tan θ^2) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin : Real.sin θ = Real.tan θ * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hcos]
  have hsq := tf71Qsub_cos_sq θ hθ0 hθ1
  have hcos2' : Real.cos (2*θ) = Real.cos θ^2 - Real.tan θ^2 * Real.cos θ^2 := by
    rw [Real.cos_two_mul', hsin]; ring
  rw [hcos2', hsq]
  field_simp

/-- `β · tan θ = (3 + tan²θ)/2`, the double-angle simplification behind the
vanishing of the trigonometric part of `tf71Q` at `t = 2γ`. -/
lemma tf71Qsub_beta_mul_tan (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) :
    tf71β θ * Real.tan θ = (3 + Real.tan θ^2)/2 := by
  have hTne : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  rw [tf71β, Real.tan_two_mul, inv_div]
  field_simp
  ring

/-- `tan θ · γ = θ/λ`, used to cancel the `θ/λ` pieces. -/
lemma tf71Qsub_tan_mul_gamma (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) (hlam : 0 < lam) :
    Real.tan θ * tf71γ θ lam = θ/lam := by
  have hTne : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  rw [tf71γ, tf71ζ]
  field_simp

theorem tf71Q_sub (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Work.ZeroFreeTables.tf71Q θ lam (2 * Work.ZeroFreeTables.tf71γ θ lam)
      - Work.ZeroFreeTables.tf71Q θ lam 0
    = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.tan θ)⁻¹ := by
  have hTne : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  have hTγ := tf71Qsub_tan_mul_gamma θ lam hθ0 hθ1 hlam
  have hS := tf71Qsub_sin_two_mul θ hθ0 hθ1
  have hC := tf71Qsub_cos_two_mul θ hθ0 hθ1
  have hβ := tf71Qsub_beta_mul_tan θ hθ0 hθ1
  -- The trigonometric bracket of `tf71Q` vanishes at `t = 2γ`.
  have hbr : (tf71Qu θ lam - tf71γ θ lam) * Real.cos (2*θ)
      + (tf71Qv θ lam - Real.tan θ * tf71γ θ lam) * Real.sin (2*θ) + (-1/lam) = 0 := by
    rw [tf71Qu, tf71Qv, hTγ, hS, hC]
    simp only [tf71A]
    field_simp
    ring_nf
    linear_combination (2 * (1 + Real.tan θ^2)) * hβ
  have hQ2 : tf71Q θ lam (2 * tf71γ θ lam) = 0 := by
    have harg : tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * θ := by
      rw [show tf71ζ θ lam * (2 * tf71γ θ lam)
            = 2 * (tf71ζ θ lam * tf71γ θ lam) from by ring, hζγ]
    simp only [tf71Q, harg,
      show (1/2) * (2 * tf71γ θ lam) = tf71γ θ lam from by ring,
      show (Real.tan θ / 2) * (2 * tf71γ θ lam) = Real.tan θ * tf71γ θ lam from by ring,
      show 2 * tf71γ θ lam - 1 / lam - 2 * tf71γ θ lam = -1/lam from by ring]
    rw [hbr]
    ring
  have hQ0 : tf71Q θ lam 0
      = tf71A θ lam * (tf71Qu θ lam + 2 * tf71γ θ lam - 1/lam) := by
    simp only [tf71Q, Real.cos_zero, Real.sin_zero, mul_zero, sub_zero, Real.exp_zero,
      mul_one, add_zero]
    ring
  rw [hQ2, hQ0]
  simp only [tf71A, tf71Qu, tf71γ, tf71ζ]
  rw [hβ]
  field_simp
  ring

end Work.ZeroFreeTables
