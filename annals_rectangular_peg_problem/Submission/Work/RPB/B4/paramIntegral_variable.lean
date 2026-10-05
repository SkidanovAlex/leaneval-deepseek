import Mathlib
import Submission.Work.RPB.B4.contDiff_parametric_integral

/-!
# Smoothness of the parametric integral with a moving upper endpoint

For a jointly `C^n` function `h : X → ℝ → F` the function

  `z ↦ ∫ s in (0 : ℝ)..z.2, h z.1 s`

is `C^n` on `X × ℝ`.

The proof is the affine substitution `s = σ * z.2`, which converts the variable-endpoint
integral into a *fixed*-interval integral of a jointly smooth integrand,

  `∫ s in 0..z.2, h z.1 s = z.2 • ∫ σ in 0..1, h z.1 (σ * z.2)`,

valid for every real `z.2` (the orientation of the interval integral takes care of the sign).
The fixed-interval statement `Work.RPB.B4.contDiff_parametric_integral` then gives the smoothness
of the second factor, and smoothness of `z ↦ z.2` gives the first.
-/

namespace Work.RPB.B4

open MeasureTheory
open scoped Interval

/-- The affine substitution in the variable-endpoint interval integral:
`∫ s in 0..c, φ s = c • ∫ σ in 0..1, φ (σ * c)`, for every real `c`. -/
theorem integral_zero_comp_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → F) (c : ℝ) :
    (∫ s in (0 : ℝ)..c, φ s) = c • ∫ σ in (0 : ℝ)..1, φ (σ * c) := by
  -- This is `intervalIntegral.smul_integral_comp_mul_add` with `a = 0`, `b = 1`, `d = 0`.
  simp

theorem paramIntegral_variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (n : ℕ) (h : X → ℝ → F) (hh : ContDiff ℝ n (fun z : X × ℝ => h z.1 z.2)) : ContDiff ℝ n (fun z : X × ℝ => ∫ s in (0:ℝ)..z.2, h z.1 s) := by
  -- Rewrite the variable-endpoint integral as `z.2` times a fixed-interval integral.
  have hsub : (fun z : X × ℝ => ∫ s in (0 : ℝ)..z.2, h z.1 s)
      = fun z : X × ℝ => z.2 • ∫ σ in (0 : ℝ)..1, h z.1 (σ * z.2) := by
    funext z
    exact integral_zero_comp_mul (fun s => h z.1 s) z.2
  rw [hsub]
  -- The substituted integrand `(σ, z) ↦ h z.1 (σ * z.2)` is jointly `C^n`.
  have hG : ContDiff ℝ n (fun w : ℝ × (X × ℝ) => h w.2.1 (w.1 * w.2.2)) := by
    have hφ : ContDiff ℝ n (fun w : ℝ × (X × ℝ) => (w.2.1, w.1 * w.2.2)) := by fun_prop
    exact hh.comp hφ
  -- So its fixed-interval integral is `C^n` in the parameter.
  have hcore : ContDiff ℝ n (fun z : X × ℝ => ∫ σ in (0 : ℝ)..1, h z.1 (σ * z.2)) :=
    contDiff_parametric_integral (fun (σ : ℝ) (z : X × ℝ) => h z.1 (σ * z.2)) 0 1 n hG
  -- Multiply by the smooth function `z ↦ z.2`.
  exact contDiff_snd.smul hcore

end Work.RPB.B4
