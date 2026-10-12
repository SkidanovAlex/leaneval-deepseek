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
# Plancherel for the `p`-convention kinetic Fourier transform

`Work.BSKinetic.plancherel_pconv`: for a smooth compactly supported real function `u` on `ℝ³`,

    (2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x u(x)²,

where `kinFT u p = ∫_y e^{-i⟪p,y⟫} u(y) dy` is the corpus's `p`-convention Fourier transform
(`Submission.BoseGases.kinFT`, equal to Mathlib's `𝓕 u` at the frequency `(2π)⁻¹ • p`).

The proof has three steps:

* `kinFT u p = 𝓕 ũ ((2π)⁻¹ • p)` where `ũ : ℝ³ → ℂ` is the complexification of `u`
  (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`);
* the change of variables `p ↦ (2π)⁻¹ • p` (`Measure.integral_comp_inv_smul_of_nonneg`,
  which holds for arbitrary functions by the "integral of a non-integrable function is zero"
  convention), which turns `(2π)⁻³ ∫_p g((2π)⁻¹ • p)` into `∫_q g(q)`;
* Plancherel for Schwartz functions, `SchwartzMap.integral_norm_sq_fourier`, applied to the
  compactly supported smooth function `ũ` (`HasCompactSupport.toSchwartzMap`), plus the
  pointwise identity `‖(x : ℂ)‖² = x²`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real FourierTransform

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option autoImplicit false

/-- **Plancherel identity for the `p`-convention kinetic Fourier transform**, for a smooth
compactly supported real function: `(2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x u(x)²`. -/
theorem plancherel_pconv (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2
      = ∫ x : EuclideanSpace ℝ (Fin 3), (u x) ^ 2 := by
  -- The complexification of `u` is smooth with compact support, hence a Schwartz function.
  have hF_smooth : ContDiff ℝ ∞ (fun x : ℝ³ => (u x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hu
  have hF_cs : HasCompactSupport (fun x : ℝ³ => (u x : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp))
  let f : SchwartzMap ℝ³ ℂ := hF_cs.toSchwartzMap hF_smooth
  have hf : (f : ℝ³ → ℂ) = fun x => (u x : ℂ) := rfl
  -- Step 1: `kinFT` is Mathlib's Fourier transform at the frequency `(2π)⁻¹ • p`.
  have hFT : ∀ p : ℝ³, Submission.BoseGases.kinFT (fun x => (u x : ℂ)) p
      = (𝓕 f) ((2 * Real.pi)⁻¹ • p) := by
    intro p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rw [← hf, ← SchwartzMap.fourier_coe]
  have hstep1 : (∫ p : ℝ³, ‖Submission.BoseGases.kinFT (fun x => (u x : ℂ)) p‖ ^ 2)
      = ∫ p : ℝ³, (fun q => ‖(𝓕 f) q‖ ^ 2) ((2 * Real.pi)⁻¹ • p) := by
    congr 1 with p
    rw [hFT p]
  -- Step 2: the change of variables `p ↦ (2π)⁻¹ • p`.
  have hstep2 : (∫ p : ℝ³, (fun q => ‖(𝓕 f) q‖ ^ 2) ((2 * Real.pi)⁻¹ • p))
      = (2 * Real.pi) ^ 3 * ∫ q : ℝ³, ‖(𝓕 f) q‖ ^ 2 := by
    have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      (f := (fun q : ℝ³ => ‖(𝓕 f) q‖ ^ 2)) (R := 2 * Real.pi)
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    rw [h2, show Module.finrank ℝ ℝ³ = 3 from by simp [EuclideanSpace], smul_eq_mul]
  -- Step 3: Plancherel for Schwartz functions.
  have hstep3 : (∫ q : ℝ³, ‖(𝓕 f) q‖ ^ 2) = ∫ x : ℝ³, (u x) ^ 2 := by
    rw [SchwartzMap.integral_norm_sq_fourier f]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hf]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two]
  rw [hstep1, hstep2, hstep3, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 3 (by positivity : (2 * Real.pi : ℝ) ≠ 0)), one_mul]

end Work.BSKinetic
