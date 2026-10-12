import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Inversion
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.kinFT_inv`

**Fourier inversion in the corpus's `p`-convention**

`Submission.BoseGases.kinFT u p = ∫_y e^{-i⟪p,y⟫}u(y)dy` is Mathlib's Fourier transform `𝓕 u`
evaluated at the frequency `(2π)⁻¹ • p` (`SmallBoxBridge.Resolve.kinFT_eq_fourier`).  The dual
inversion formula therefore reads

  `f x = (2π)^{-3} ∫_p e^{i⟪p,x⟫} \hat f(p) dp`,

which is the statement of this file.

## Proof

1. Write the integrand with the substitution `p = (2π) • w`:
   `e^{i⟪p,x⟫}·kinFT f p = F ((2π)⁻¹ • p)` where `F w = e^{i⟪(2π)•w,x⟫}·𝓕 f w`.
2. The Haar-measure scaling `Measure.integral_comp_inv_smul_of_nonneg` turns
   `∫_p F ((2π)⁻¹ • p)` into `(2π)^{finrank} • ∫_w F w = (2π)³·∫_w F w`.
3. `∫_w F w = 𝓕⁻ (𝓕 f) x` by `Real.fourierInv_eq'`, using `⟪(2π)•w,x⟫ = 2π⟪w,x⟫`.
4. Fourier inversion `MeasureTheory.Integrable.fourierInv_fourier_eq` (this is where
   integrability of `f` and of `𝓕 f`, and continuity of `f`, enter) gives `𝓕⁻ (𝓕 f) x = f x`.
5. The prefactors `(2π)⁻³` and `(2π)³` cancel.
-/

noncomputable section

namespace Work.BoseBoxFock.FRK

open MeasureTheory

set_option maxHeartbeats 800000

theorem kinFT_inv {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf1 : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.Integrable (FourierTransform.fourier f)) (hfc : Continuous f)
    (x : EuclideanSpace ℝ (Fin 3)) :
    f x = (((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * MeasureTheory.integral MeasureTheory.volume
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * Submission.BoseGases.kinFT f p) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hR : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hRne : (2 * Real.pi) ≠ 0 := by positivity
  -- the integrand after the substitution `p = (2π) • w`
  set F : EuclideanSpace ℝ (Fin 3) → ℂ := fun w =>
    Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi) • w) x : ℂ)) *
      FourierTransform.fourier f w with hFdef
  -- step 1: `kinFT` is `𝓕` at the rescaled frequency
  have hpointwise : ∀ p : EuclideanSpace ℝ (Fin 3),
      Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * Submission.BoseGases.kinFT f p
        = F ((2 * Real.pi)⁻¹ • p) := by
    intro p
    have hp : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • p) = p := by
      rw [smul_smul, mul_inv_cancel₀ hRne, one_smul]
    simp only [hFdef]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier f p, hp]
  have hI1 : (∫ p : EuclideanSpace ℝ (Fin 3),
        Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * Submission.BoseGases.kinFT f p)
      = ∫ p : EuclideanSpace ℝ (Fin 3), F ((2 * Real.pi)⁻¹ • p) :=
    integral_congr_ae (Filter.Eventually.of_forall hpointwise)
  -- step 2: the Haar-measure substitution `p ↦ (2π) • w`
  have hI2 : (∫ p : EuclideanSpace ℝ (Fin 3), F ((2 * Real.pi)⁻¹ • p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ∫ w : EuclideanSpace ℝ (Fin 3), F w := by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume F hR, hfin, Complex.real_smul]
  -- step 3: the remaining integral is `𝓕⁻ (𝓕 f) x`
  have hI3 : (∫ w : EuclideanSpace ℝ (Fin 3), F w)
      = FourierTransform.fourierInv (FourierTransform.fourier f) x := by
    simp only [hFdef]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with w
    rw [smul_eq_mul]
    congr 1
    rw [real_inner_smul_left]
    push_cast
    ring_nf
  -- step 4: Fourier inversion
  have hI4 : FourierTransform.fourierInv (FourierTransform.fourier f) x = f x :=
    congrFun (hfc.fourierInv_fourier_eq hf1 hf2) x
  -- step 5: the scalar prefactor `(2π)⁻³·(2π)³ = 1` (note the two sides are
  -- `(((2π)^3)⁻¹ : ℝ)` coerced and `((2π)^3 : ℂ)⁻¹`, related by `Complex.ofReal_inv`)
  have key : ((((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ) * MeasureTheory.integral MeasureTheory.volume
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (Complex.I * ((inner ℝ p x : ℝ) : ℂ)) * Submission.BoseGases.kinFT f p))
      = f x := by
    rw [hI1, hI2, hI3, hI4, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 3 ≠ 0), Complex.ofReal_one, one_mul]
  exact key.symm

end Work.BoseBoxFock.FRK
