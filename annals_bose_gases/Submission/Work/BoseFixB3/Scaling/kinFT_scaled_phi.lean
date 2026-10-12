import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixB3.Scaling.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Scaling.kinFT_scaled_phi` — the `p`-convention Fourier transform scales

The profile `φ = χ²` is dilated by `ℓ⁻¹` in the localisation `χ_Λ² = φ(ℓ⁻¹ • ·)`.
This file records the resulting scaling of the `p`-convention Fourier transform
`Submission.BoseGases.kinFT`: substituting `z = ℓ • y` in
`∫_z e^{-i⟪p,z⟫} φ(ℓ⁻¹ • z) dz` (the Haar measure of `ℝ³` scales by `ℓ³`) gives

`kinFT (φ(ℓ⁻¹ • ·)) p = ℓ³ · kinFT φ (ℓ • p)`.

Formally this is `Measure.integral_comp_inv_smul_of_nonneg` (`∫ z, f (ℓ⁻¹ • z) = ℓ³ • ∫ y, f y`
for the additive Haar measure on the finite-dimensional real space `ℝ³`), applied to
`f y = e^{-i⟪ℓp,y⟫} φ(y)`; the identity `⟪ℓp, ℓ⁻¹ z⟫ = ⟪p, z⟫` matches the two oscillatory
factors.
-/

noncomputable section

open MeasureTheory Measure
open scoped Real

namespace Work.BoseFixB3.Scaling

theorem kinFT_scaled_phi (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)) p
      = (ℓ ^ 3 : ℝ) • Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC (ℓ • p) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- The oscillatory factors agree after the substitution `z = ℓ • y`, since `⟪ℓp, ℓ⁻¹z⟫ = ⟪p,z⟫`.
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * ↑(inner ℝ p z))) * (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)
        = Complex.exp (-(Complex.I * ↑(inner ℝ (ℓ • p) (ℓ⁻¹ • z))))
            * (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ) := by
    intro z
    have hin : inner ℝ (ℓ • p) (ℓ⁻¹ • z) = inner ℝ p z := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul]
    rw [hin]
  simp only [Submission.BoseGases.kinFT, Work.BoseFixB3.Scaling.phiC]
  -- Rewrite the integrand as `H (ℓ⁻¹ • z)` with `H y = e^{-i⟪ℓp,y⟫} φ(y)`.
  rw [show (∫ z : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * ↑(inner ℝ p z))) * (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ))
      = ∫ z : EuclideanSpace ℝ (Fin 3),
        (fun y : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * ↑(inner ℝ (ℓ • p) y))) * (Work.BoseFixB3.Scaling.phi y : ℂ))
          (ℓ⁻¹ • z) from by
        apply integral_congr_ae
        filter_upwards with z
        exact hpt z]
  -- Change variables `z = ℓ • y` in the additive Haar measure on `ℝ³` (`ℓ > 0`, `finrank ℝ ℝ³ = 3`).
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * ↑(inner ℝ (ℓ • p) y))) * (Work.BoseFixB3.Scaling.phi y : ℂ))
      hℓ.le, hfin]

end Work.BoseFixB3.Scaling
