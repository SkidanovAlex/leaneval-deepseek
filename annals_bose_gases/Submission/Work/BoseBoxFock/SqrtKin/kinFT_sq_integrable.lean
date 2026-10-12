import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.SqrtKinDefs
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `p ↦ ‖kinFT g p‖²` for smooth compactly supported complex `g`

`Submission.BoseGases.kinFT g p = ∫_y e^{−i⟪p,y⟫}g y dy` is Mathlib's Fourier transform at the
rescaled frequency `(2π)⁻¹ • p` (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`).  A smooth
compactly supported `g : ℝ³ → ℂ` is a Schwartz function (`HasCompactSupport.toSchwartzMap`), whose
Fourier transform `𝓕 g` is Schwartz again; hence `ξ ↦ ‖(𝓕 g) ξ‖²` is integrable
(`SchwartzMap.memLp`, `MemLp.integrable_sq`).  Precomposing with the dilation
`p ↦ (2π)⁻¹ • p` preserves integrability (`Integrable.comp_smul`), which gives the claim.

This is the complex-valued companion of `Work.BSKinetic.integrable_kinFT_sq` (stated there for
real `u`); the proof is the same, carried out directly for complex `g`.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform ContDiff

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem kinFT_sq_integrable {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- `g` as a Schwartz function
  let F : SchwartzMap ℝ³ ℂ := hgc.toSchwartzMap hg
  have hF_coe : (F : ℝ³ → ℂ) = g := rfl
  -- `𝓕 F ∈ L²`, hence `ξ ↦ ‖(𝓕 F) ξ‖²` is integrable
  have hmem : MemLp (fun ξ : ℝ³ => ‖(𝓕 F) ξ‖) 2 (volume : Measure ℝ³) :=
    (SchwartzMap.memLp (𝓕 F) 2 (volume : Measure ℝ³)).norm
  have hint : Integrable (fun ξ : ℝ³ => ‖(𝓕 F) ξ‖ ^ 2) := hmem.integrable_sq
  -- precomposition with the dilation `p ↦ (2π)⁻¹ • p` preserves integrability
  have hcomp : Integrable (fun p : ℝ³ => ‖(𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p)‖ ^ 2) :=
    hint.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  refine hcomp.congr (Filter.Eventually.of_forall (fun p => ?_))
  beta_reduce
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hF_coe, SchwartzMap.fourier_coe]

end Work.BoseBoxFock.SqrtKin
