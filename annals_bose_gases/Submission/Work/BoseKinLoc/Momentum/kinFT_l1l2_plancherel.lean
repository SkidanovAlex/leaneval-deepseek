import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Plancherel for the `p`-convention kinetic Fourier transform, L¹ ∩ L² version

For `F : ℝ³ → ℂ` in `L¹ ∩ L²` (the precise hypotheses are `Integrable F` and `MemLp F 2`),

`∫_p ‖kinFT F p‖² = (2π)³ ∫_x ‖F x‖²`,

where `kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy` is the corpus's `p`-convention Fourier transform.

This is the (`L¹ ∩ L²`, as opposed to Schwartz) version of
`Work.BoseKinLoc.Momentum.plancherel_kinFT_schwartz`; the argument is the same three steps:

* `kinFT F p = 𝓕 F ((2π)⁻¹ • p)` (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`, valid for
  *arbitrary* `F`);
* the change of variables `p ↦ (2π)⁻¹ • p` (`Measure.integral_comp_inv_smul_of_nonneg`,
  valid for arbitrary functions, the Bochner convention settling the non-integrable case);
* Plancherel for `L¹ ∩ L²` functions
  (`Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2`).
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.Momentum

theorem kinFT_l1l2_plancherel {F : EuclideanSpace ℝ (Fin 3) → ℂ} (h1 : MeasureTheory.Integrable F) (h2 : MeasureTheory.MemLp F 2 MeasureTheory.volume) : ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2 = (2 * Real.pi) ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), ‖F x‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Step 1: `kinFT F` is Mathlib's Fourier transform at the frequency `(2π)⁻¹ • p`.
  have hcongr : (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = fun p : EuclideanSpace ℝ (Fin 3) =>
          (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖(FourierTransform.fourier F) ξ‖ ^ 2)
            ((2 * Real.pi)⁻¹ • p) := by
    funext p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  -- Step 2: the change of variables `p ↦ (2π)⁻¹ • p`.
  rw [hcongr, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
    (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖(FourierTransform.fourier F) ξ‖ ^ 2) hpi.le]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp [EuclideanSpace],
    smul_eq_mul]
  -- Step 3: Plancherel for an `L¹ ∩ L²` function.
  rw [Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2 h1 h2]

end Work.BoseKinLoc.Momentum
