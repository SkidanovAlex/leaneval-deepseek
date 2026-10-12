import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the `p`-convention kinetic energy density `‖kinFT u‖²`

For a smooth compactly supported real one-body state `u : ℝ³ → ℝ`, the function

    `p ↦ ‖kinFT (u : ℂ) p‖²`

is integrable on `ℝ³`.  This is the *unweighted* companion of the weighted statement
`‖p‖²·‖kinFT u p‖² ∈ L¹` (`Work.SmallBoxTBWord.integrable_kinFT_energy_cspt`), and it is
exactly what makes the `p`-integrals appearing in the kinetic bridge non-junk.

The proof is the `L²` half of Plancherel.  `u` is smooth with compact support, hence so is
its complexification `g = (u : ℂ)`, which is therefore a Schwartz function: let
`F : SchwartzMap ℝ³ ℂ` be Mathlib's Schwartz representative of `g`.  A Schwartz function
belongs to every `Lᵖ` with respect to Lebesgue measure (`SchwartzMap.memLp`), so
`ξ ↦ ‖(𝓕 F) ξ‖²` is integrable.  The `p`-convention transform `kinFT` is Mathlib's Fourier
transform precomposed with the dilation `p ↦ (2π)⁻¹ • p`
(`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`), a linear scaling of `ℝ³` which preserves
integrability (`Integrable.comp_smul`).
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform ContDiff

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The squared `p`-convention Fourier transform of a smooth compactly supported state is
integrable.** -/
theorem integrable_kinFT_sq (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u) (hcs : HasCompactSupport u) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => (u x : ℂ)) p‖ ^ 2) := by
  have hucs : HasCompactSupport (fun z : ℝ³ => (u z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have husm : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (u z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hu
  -- the complexification of `u` as a Schwartz function
  let F : SchwartzMap ℝ³ ℂ := hucs.toSchwartzMap husm
  have hF_coe : (F : ℝ³ → ℂ) = fun z => (u z : ℂ) := rfl
  -- `𝓕 F ∈ L²`, hence `ξ ↦ ‖(𝓕 F) ξ‖²` is integrable
  have hmem : MemLp (fun ξ : ℝ³ => ‖(𝓕 F) ξ‖) 2 (volume : Measure ℝ³) :=
    (SchwartzMap.memLp (𝓕 F) 2 (volume : Measure ℝ³)).norm
  have hint : Integrable (fun ξ : ℝ³ => ‖(𝓕 F) ξ‖ ^ 2) := hmem.integrable_sq
  -- precomposing with the dilation `p ↦ (2π)⁻¹ • p` preserves integrability
  have hcomp : Integrable (fun p : ℝ³ => ‖(𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p)‖ ^ 2) :=
    hint.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  refine hcomp.congr (Filter.Eventually.of_forall (fun p => ?_))
  beta_reduce
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hF_coe, SchwartzMap.fourier_coe]

end Work.BSKinetic
