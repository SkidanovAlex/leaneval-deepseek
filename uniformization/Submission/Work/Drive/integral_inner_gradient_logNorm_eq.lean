import Submission.Work.Drive.polarPtBasics
import Submission.Work.Drive.integral_polar_deriv_eq
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero

/-!
# The fundamental-solution identity (pole term of the Dirichlet/Weyl route)

`Work.Drive.integral_inner_gradient_logNorm_eq`: `∫_ℂ ⟪∇(−log‖·−a‖), ∇ψ⟫ = 2π ψ a` for `ψ ∈ C¹`
with compact support.

This module exists to glue two files that cannot import each other:
`greenSymmetryRegion.lean` (which carries the polar reduction `integral_integrand_polar`, the
conditional angular integration `setIntegral_polar_eq_two_pi_mul_of_integrable`, and the
integrability `integrableOn_deriv_polarPt`) and `integral_polar_deriv_eq.lean` (the per-angle
fundamental theorem of calculus, proved separately, which *imports the former*).
-/

noncomputable section

open MeasureTheory

namespace Work.Drive

/-- **The fundamental-solution identity.**  For `ψ ∈ C¹` with compact support,
`∫_ℂ ⟪∇(−log‖·−a‖), ∇ψ⟫ = 2π ψ a` — the pole term of the Dirichlet/Weyl route to the symmetry of
the Green function. -/
theorem integral_inner_gradient_logNorm_eq {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    (∫ z : ℂ, inner (𝕜 := ℝ)
        (gradient (fun z : ℂ => - Real.log ‖z - a‖) z) (gradient ψ z))
      = 2 * Real.pi * ψ a :=
  (integral_integrand_polar hψ).trans
    (setIntegral_polar_eq_two_pi_mul_of_integrable hψ hψc
      (integrableOn_deriv_polarPt hψ hψc)
      (fun θ => integral_polar_deriv_eq hψ hψc θ))

section GradientAlgebra

/-- **Additivity of the gradient** (missing from Mathlib).  Since `gradient` is
`(InnerProductSpace.toDual 𝕜 F).symm ∘ fderiv 𝕜`, this is the additivity of `fderiv` transported
along the continuous linear equivalence `toDual`. -/
theorem gradient_add {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] {f g : F → 𝕜} {z : F} (hf : DifferentiableAt 𝕜 f z)
    (hg : DifferentiableAt 𝕜 g z) :
    gradient (fun y => f y + g y) z = gradient f z + gradient g z := by
  have h1 : fderiv 𝕜 (fun y => f y + g y) z = fderiv 𝕜 f z + fderiv 𝕜 g z :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  simp only [gradient]
  rw [h1, map_add]

/-- **Subtractivity of the gradient** (missing from Mathlib). -/
theorem gradient_sub {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] {f g : F → 𝕜} {z : F} (hf : DifferentiableAt 𝕜 f z)
    (hg : DifferentiableAt 𝕜 g z) :
    gradient (fun y => f y - g y) z = gradient f z - gradient g z := by
  have h1 : fderiv 𝕜 (fun y => f y - g y) z = fderiv 𝕜 f z - fderiv 𝕜 g z :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  simp only [gradient]
  rw [h1, map_sub]

end GradientAlgebra

section PoleTerm

variable {G χ h : ℂ → ℝ} {a : ℂ}

/-- **The pole term of the Dirichlet/Weyl expansion.**  With `h` harmonic on all of `ℂ` (in the
application `h` is the harmonic part of the chart-pullback of `gA`, extended across the pole by the
removable singularity), `χ · G` a `C¹` compactly supported test function and `χ a = 1`:
`∫_ℂ ⟪∇(−log‖·−a‖ + h), ∇(χ·G)⟫ = 2π G a`.  The harmonic part contributes nothing
(`Work.Analysis.Harmonic.integral_inner_gradient_eq_zero`) and the singular part contributes the
fundamental-solution value (`integral_inner_gradient_logNorm_eq`). -/
theorem integral_inner_gradient_log_add_eq
    (hχG : ContDiff ℝ 1 (fun z : ℂ => χ z * G z))
    (hχGc : HasCompactSupport (fun z : ℂ => χ z * G z))
    (hh : ∀ z, InnerProductSpace.HarmonicAt h z) (hχa : χ a = 1)
    (hint1 : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient (fun z : ℂ => χ z * G z) z)))
    (hint2 : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient h z) (gradient (fun z : ℂ => χ z * G z) z))) :
    (∫ z : ℂ, inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖ + h y) z)
        (gradient (fun z : ℂ => χ z * G z) z))
      = 2 * Real.pi * G a := by
  set F : ℂ → ℝ := fun z => χ z * G z with hF
  have hχG' : ContDiff ℝ 1 F := by rw [hF]; exact hχG
  have hχGc' : HasCompactSupport F := by rw [hF]; exact hχGc
  have hae : (fun z : ℂ => inner (𝕜 := ℝ)
        (gradient (fun y : ℂ => -Real.log ‖y - a‖ + h y) z) (gradient F z))
      =ᵐ[volume] fun z : ℂ =>
          inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z) (gradient F z)
        + inner (𝕜 := ℝ) (gradient h z) (gradient F z) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton a)] with z hz
    have hza : z ≠ a := by simpa using hz
    have hLd : DifferentiableAt ℝ (fun y : ℂ => -Real.log ‖y - a‖) z :=
      (hasFDerivAt_neg_log_norm_sub hza).differentiableAt
    have hhd : DifferentiableAt ℝ h z := ((hh z).1).differentiableAt (by norm_num)
    rw [gradient_add hLd hhd, inner_add_left]
  rw [integral_congr_ae hae, integral_add hint1 hint2]
  have h1 : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - a‖) z)
      (gradient F z)) = 2 * Real.pi * F a :=
    integral_inner_gradient_logNorm_eq hχG' hχGc'
  have h2 : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient h z) (gradient F z)) = 0 :=
    Work.Analysis.Harmonic.integral_inner_gradient_eq_zero (fun z _ => hh z) hχG' hχGc'
  rw [h1, h2]
  simp only [hF, hχa, one_mul, add_zero]

end PoleTerm

end Work.Drive
