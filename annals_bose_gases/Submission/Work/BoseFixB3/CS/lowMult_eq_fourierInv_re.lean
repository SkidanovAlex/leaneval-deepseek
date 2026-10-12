import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.lowMult_eq_fourierInv_re`

The degenerate-cutoff identity for the corpus's low-momentum multiplier
`Work.BoseBoxFix.lowMult fc κ ℓ ψ x` (FS `f_L(√−Δ)ψ` on the box `acube ℓ`, in the corpus's
`p`-convention `kinFT`):

  `lowMult fc κ ℓ ψ x = (𝓕⁻ (𝓕 (1_{acube ℓ}ψ)) x).re`   whenever `κ ≤ 0`.

## Proof

`LowCut.f s = 1` for `s ≤ 1`, and for `κ ≤ 0` one has `‖p‖ / κ ≤ 0 ≤ 1`, so the symbol
`fc.f (‖p‖ / κ)` is identically `1` and the multiplier collapses to the identity multiplier.
The remaining identity is the Haar-measure substitution `p = (2π) • w` in the defining
integral of `lowMult`, together with the convention bridge
`kinFT g p = 𝓕 g ((2π)⁻¹ • p)` (`SmallBoxBridge.Resolve.kinFT_eq_fourier`):

  `(2π)^{-3} ∫_p e^{i⟪p,x⟫} kinFT g p = ∫_w e^{2πi⟪w,x⟫} 𝓕 g w = (𝓕⁻ 𝓕 g) x`.

Note that no Fourier-inversion theorem is used (and none is available: `ψ` is an arbitrary
function): the identity is valid for every `ψ`, as an identity between integrals.
The substitution is `Measure.integral_comp_inv_smul_of_nonneg` for Lebesgue measure on
`ℝ³` (`finrank ℝ ℝ³ = 3`).
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseFixB3.CS

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem lowMult_eq_fourierInv_re {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : κ ≤ 0)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = (FourierTransformInv.fourierInv
          (FourierTransform.fourier
            (fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ))) x).re := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hR : (2 * Real.pi) ≠ 0 := by positivity
  set g : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hgdef
  -- The cutoff is identically `1` because `κ ≤ 0`.
  have hcut : ∀ p : EuclideanSpace ℝ (Fin 3), fc.f (‖p‖ / κ) = 1 := fun p =>
    fc.one _ (le_trans (div_nonpos_of_nonneg_of_nonpos (norm_nonneg p) hκ) zero_le_one)
  -- consequently the defining integral of `lowMult` loses its symbol factor
  have hcut_int :
      (∫ p : EuclideanSpace ℝ (Fin 3),
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            Submission.BoseGases.kinFT g p)
        = ∫ p : EuclideanSpace ℝ (Fin 3),
            Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * Submission.BoseGases.kinFT g p := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hcut p]
    simp
  -- the integrand after the substitution `p = (2π) • w`
  set F : EuclideanSpace ℝ (Fin 3) → ℂ := fun w =>
    Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi) • w) x : ℂ)) *
      FourierTransform.fourier g w with hFdef
  have hpointwise : ∀ p : EuclideanSpace ℝ (Fin 3),
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * Submission.BoseGases.kinFT g p
        = F ((2 * Real.pi)⁻¹ • p) := by
    intro p
    have hp : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • p) = p := by
      rw [smul_smul, mul_inv_cancel₀ hR, one_smul]
    simp only [hFdef]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier g p, hp]
  have hI1 : (∫ p : EuclideanSpace ℝ (Fin 3),
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * Submission.BoseGases.kinFT g p)
      = ∫ p : EuclideanSpace ℝ (Fin 3), F ((2 * Real.pi)⁻¹ • p) :=
    integral_congr_ae (Filter.Eventually.of_forall hpointwise)
  -- the Haar-measure substitution `p ↦ (2π) • w`
  have hI2 : (∫ p : EuclideanSpace ℝ (Fin 3), F ((2 * Real.pi)⁻¹ • p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ∫ w : EuclideanSpace ℝ (Fin 3), F w := by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume F
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hfin, Complex.real_smul]
  -- the substituted integral is the inverse Fourier transform
  have hI3 : (∫ w : EuclideanSpace ℝ (Fin 3), F w)
      = FourierTransform.fourierInv (FourierTransform.fourier g) x := by
    simp only [hFdef]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with w
    rw [smul_eq_mul]
    congr 1
    rw [real_inner_smul_left]
    push_cast
    ring_nf
  have hcoef : ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * (((2 * Real.pi) ^ 3 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 3 ≠ 0),
      Complex.ofReal_one]
  have hmain : (((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ p : EuclideanSpace ℝ (Fin 3),
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            Submission.BoseGases.kinFT g p)
      = FourierTransform.fourierInv (FourierTransform.fourier g) x := by
    rw [hcut_int, hI1, hI2, hI3, ← mul_assoc, hcoef, one_mul]
  rw [Work.BoseBoxFix.lowMult, ← hgdef]
  exact congrArg Complex.re hmain

end Work.BoseFixB3.CS
