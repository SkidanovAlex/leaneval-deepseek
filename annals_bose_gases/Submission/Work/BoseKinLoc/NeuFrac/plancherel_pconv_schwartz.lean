import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Plancherel for the `p`-convention kinetic Fourier transform, Schwartz version

For a Schwartz function `F : 𝓢(ℝ³, ℂ)`,

    `(2π)⁻³ ∫_p ‖kinFT F p‖² = ∫_x ‖F x‖²`,

where `Submission.BoseGases.kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy` is the corpus's `p`-convention
Fourier transform.

This is the general (non-compactly-supported) companion of
`Work.BSKinetic.plancherel_pconv`, which covers smooth compactly supported real functions.
The proof has three steps:

* `kinFT F p = 𝓕 F ((2π)⁻¹ • p)` for Mathlib's Fourier transform `𝓕`
  (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`);
* the change of variables `p ↦ (2π)⁻¹ • p` on `ℝ³` (`Measure.integral_comp_inv_smul_of_nonneg`,
  whose validity for *arbitrary* functions relies on the "integral of a non-integrable
  function is zero" convention), turning `(2π)⁻³ ∫_p g((2π)⁻¹ • p)` into `∫_q g(q)`;
* Plancherel for Schwartz functions, `SchwartzMap.integral_norm_sq_fourier`.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.NeuFrac

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem plancherel_pconv_schwartz (F : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.kinFT (F : EuclideanSpace ℝ (Fin 3) → ℂ) p‖ ^ 2
      = ∫ x : EuclideanSpace ℝ (Fin 3), ‖F x‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 : ℝ) * Real.pi ≠ 0 := hpi.ne'
  -- Step 1: `kinFT` is Mathlib's Fourier transform at the frequency `(2π)⁻¹ • p`.
  have hkin : ∀ p : ℝ³, Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p
      = (FourierTransform.fourier (F : ℝ³ → ℂ)) ((2 * Real.pi)⁻¹ • p) :=
    fun p => Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (F : ℝ³ → ℂ) p
  have hcongr : (fun p : ℝ³ => ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2)
      = fun p : ℝ³ =>
          (fun ξ : ℝ³ => ‖(FourierTransform.fourier (F : ℝ³ → ℂ)) ξ‖ ^ 2)
            ((2 * Real.pi)⁻¹ • p) := by
    funext p
    rw [hkin p]
  -- Step 2: the change of variables `p ↦ (2π)⁻¹ • p` (`p = 2π·q`).
  have hstep1 : (∫ p : ℝ³, ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2)
      = (2 * Real.pi) ^ 3
          * ∫ ξ : ℝ³, ‖(FourierTransform.fourier (F : ℝ³ → ℂ)) ξ‖ ^ 2 := by
    rw [hcongr]
    rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
      (fun ξ : ℝ³ => ‖(FourierTransform.fourier (F : ℝ³ → ℂ)) ξ‖ ^ 2) hpi.le]
    rw [show Module.finrank ℝ ℝ³ = 3 from by simp [EuclideanSpace], smul_eq_mul]
  -- Step 3: Plancherel for Schwartz functions.
  rw [hstep1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hne), one_mul]
  simpa only [SchwartzMap.fourier_coe] using SchwartzMap.integral_norm_sq_fourier F

end Work.BoseKinLoc.NeuFrac
